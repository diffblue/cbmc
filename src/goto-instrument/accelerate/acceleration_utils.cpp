#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <algorithm>
#include <ctime>

#include <goto-programs/goto_program.h>
#include <goto-programs/wp.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <analyses/goto_check.h>

#include <ansi-c/expr2c.h>

#include <util/symbol_table.h>
#include <util/options.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/i2string.h>
#include <util/find_symbols.h>
#include <util/rename.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/arith_tools.h>

#include "acceleration_utils.h"
#include "accelerator.h"
#include "util.h"
#include "cone_of_influence.h"
#include "overflow_instrumenter.h"

#define DEBUG

void acceleration_utilst::gather_rvalues(const exprt &expr,
    expr_sett &rvalues) {
  if (expr.id() == ID_symbol ||
      expr.id() == ID_index ||
      expr.id() == ID_member ||
      expr.id() == ID_dereference) {
    rvalues.insert(expr);
  } else {
    forall_operands(it, expr) {
      gather_rvalues(*it, rvalues);
    }
  }
}

void acceleration_utilst::find_modified(goto_programt &body,
    expr_sett &modified) {
  find_modified(body.instructions, modified);
}

void acceleration_utilst::find_modified(goto_programt::instructionst &instructions,
    expr_sett &modified) {
  for (goto_programt::instructionst::iterator it = instructions.begin();
       it != instructions.end();
       ++it) {
    find_modified(it, modified);
  }
}


void acceleration_utilst::find_modified(patht &path,
    expr_sett &modified) {
  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    find_modified(it->loc, modified);
  }
}

void acceleration_utilst::find_modified(
    natural_loops_mutablet::natural_loopt &loop,
    expr_sett &modified) {
  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    find_modified(*it, modified);
  }
}

void acceleration_utilst::find_modified(goto_programt::targett t,
  expr_sett &modified) {
  if (t->is_assign()) {
    code_assignt assignment = to_code_assign(t->code);
    modified.insert(assignment.lhs());
  }
}


bool acceleration_utilst::check_inductive(map<exprt, polynomialt> polynomials,
                                              patht &path) {
  // Checking that our polynomial is inductive with respect to the loop body is
  // equivalent to checking safety of the following program:
  //
  // assume (target1 == polynomial1);
  // assume (target2 == polynomial2)
  // ...
  // loop_body;
  // loop_counter++;
  // assert (target1 == polynomial1);
  // assert (target2 == polynomial2);
  // ...
  scratch_programt program(symbol_table);
  vector<exprt> polynomials_hold;
  substitutiont substitution;

  stash_polynomials(program, polynomials, substitution, path);
 
  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    exprt holds = equal_exprt(it->first, it->second.to_expr());
    program.add_instruction(ASSUME)->guard = holds;

    polynomials_hold.push_back(holds);
  }

  program.append_path(path);

  codet inc_loop_counter = code_assignt(loop_counter,
                                        plus_exprt(loop_counter, from_integer(1, loop_counter.type())));
  program.add_instruction(ASSIGN)->code = inc_loop_counter;

  ensure_no_overflows(program);

  for (vector<exprt>::iterator it = polynomials_hold.begin();
       it != polynomials_hold.end();
       ++it) {
    program.add_instruction(ASSERT)->guard = *it;
  }

#ifdef DEBUG
  std::cout << "Checking following program for inductiveness:" << endl;
  program.output(ns, "", std::cout);
#endif

  try {
    if (program.check_sat()) {
      // We found a counterexample to inductiveness... :-(
  #ifdef DEBUG
      std::cout << "Not inductive!" << endl;
  #endif
    return false;
    } else {
      return true;
    }
  } catch (string s) {
    std::cout << "Error in inductiveness SAT check: " << s << endl;
    return false;
  } catch (const  char *s) {
    std::cout << "Error in inductiveness SAT check: " << s << endl;
    return false;
  }
}

void acceleration_utilst::stash_polynomials(
    scratch_programt &program,
    map<exprt, polynomialt> &polynomials,
    substitutiont &substitution,
    patht &path) {
  expr_sett modified;

  find_modified(path, modified);
  stash_variables(program, modified, substitution);

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    it->second.substitute(substitution);
  }
}

void acceleration_utilst::stash_variables(scratch_programt &program,
                                              expr_sett modified,
                                              substitutiont &substitution) {
  find_symbols_sett vars;

  for (expr_sett::iterator it = modified.begin();
       it != modified.end();
       ++it) {
    find_symbols(*it, vars);
  }

  irep_idt loop_counter_name = to_symbol_expr(loop_counter).get_identifier();
  vars.erase(loop_counter_name);

  for (find_symbols_sett::iterator it = vars.begin();
       it != vars.end();
       ++it) {
    symbolt orig = symbol_table.lookup(*it);
    symbolt stashed_sym = fresh_symbol("polynomial::stash", orig.type);
    substitution[orig.symbol_expr()] = stashed_sym.symbol_expr();
    program.assign(stashed_sym.symbol_expr(), orig.symbol_expr());
  }
}

/*
 * Finds a precondition which guarantees that all the assumptions and assertions
 * along this path hold.
 *
 * This is not the weakest precondition, since we make underapproximations due
 * to aliasing.
 */

exprt acceleration_utilst::precondition(patht &path) {
  exprt ret = false_exprt();

  for (patht::reverse_iterator r_it = path.rbegin();
       r_it != path.rend();
       ++r_it) {
    goto_programt::const_targett t = r_it->loc;

    if (t->is_assign()) {
      // XXX Need to check for aliasing...
      const code_assignt &assignment = to_code_assign(t->code);
      const exprt &lhs = assignment.lhs();
      const exprt &rhs = assignment.rhs();

      if (lhs.id() == ID_symbol ||
          lhs.id() == ID_index ||
          lhs.id() == ID_dereference) {
        replace_expr(lhs, rhs, ret);
      } else {
        throw "Couldn't take WP of " + expr2c(lhs, ns) + " = " + expr2c(rhs, ns);
      }
    } else if (t->is_assume() || t->is_assert()) {
      ret = implies_exprt(t->guard, ret);
    } else {
      // Ignore.
    }

    if (!r_it->guard.is_true() && !r_it->guard.is_nil()) {
      // The guard isn't constant true, so we need to accumulate that too.
      ret = implies_exprt(r_it->guard, ret);
    }
  }

  // Hack: replace array accesses with nondet.
  expr_mapt array_abstractions;
  //abstract_arrays(ret, array_abstractions);

  simplify(ret, ns);

  return ret;
}

void acceleration_utilst::abstract_arrays(exprt &expr, expr_mapt &abstractions) {
  if (expr.id() == ID_index ||
      expr.id() == ID_dereference) {
    expr_mapt::iterator it = abstractions.find(expr);

    if (it == abstractions.end()) {
      symbolt sym = fresh_symbol("accelerate::array_abstraction", expr.type());
      abstractions[expr] = sym.symbol_expr();
      expr = sym.symbol_expr();
    } else {
      expr = it->second;
    }
  } else {
    Forall_operands(it, expr) {
      abstract_arrays(*it, abstractions);
    }
  }
}

void acceleration_utilst::push_nondet(exprt &expr) {
  Forall_operands(it, expr) {
    push_nondet(*it);
  }

  if (expr.id() == ID_not &&
      expr.op0().id() == ID_nondet) {
    expr = side_effect_expr_nondett(expr.type());
  } else if (expr.id() == ID_equal ||
             expr.id() == ID_lt ||
             expr.id() == ID_gt ||
             expr.id() == ID_le ||
             expr.id() == ID_ge) {
    if (expr.op0().id() == ID_nondet ||
        expr.op1().id() == ID_nondet) {
      expr = side_effect_expr_nondett(expr.type());
    }
  }
}



bool acceleration_utilst::do_assumptions(map<exprt, polynomialt> polynomials,
                                             patht &path,
                                             exprt &guard) {
  // We want to check that if an assumption fails, the next iteration can't be
  // feasible again.  To do this we check the following program for safety:
  //
  // loop_counter = 1;
  // assume(target1 == polynomial1);
  // assume(target2 == polynomial2);
  // ...
  // assume(precondition);
  //
  // loop_counter = *;
  // target1 = polynomial1);
  // target2 = polynomial2);
  // ...
  // assume(!precondition);
  //
  // loop_counter++;
  //
  // target1 = polynomial1;
  // target2 = polynomial2;
  // ...
  //
  // assume(no overflows in above program)
  // assert(!precondition);

  exprt condition = precondition(path);
  scratch_programt program(symbol_table); 

  substitutiont substitution;
  stash_polynomials(program, polynomials, substitution, path);

  vector<exprt> polynomials_hold;

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    exprt lhs = it->first;
    exprt rhs = it->second.to_expr();

    polynomials_hold.push_back(equal_exprt(lhs, rhs));
  }

  program.assign(loop_counter, from_integer(0, loop_counter.type()));

  for (vector<exprt>::iterator it = polynomials_hold.begin();
       it != polynomials_hold.end();
       ++it) {
    program.assume(*it);
  }

  program.assume(not_exprt(condition));

  program.assign(loop_counter, side_effect_expr_nondett(loop_counter.type()));

  for (map<exprt, polynomialt>::iterator p_it = polynomials.begin();
       p_it != polynomials.end();
       ++p_it) {
    program.assign(p_it->first, p_it->second.to_expr());
  }

  program.assume(condition);
  program.assign(loop_counter,
                 plus_exprt(loop_counter, from_integer(1, loop_counter.type())));

  for (map<exprt, polynomialt>::iterator p_it = polynomials.begin();
       p_it != polynomials.end();
       ++p_it) {
    program.assign(p_it->first, p_it->second.to_expr());
  }

  ensure_no_overflows(program);

  program.add_instruction(ASSERT)->guard = condition;

  guard = not_exprt(condition);
  simplify(guard, ns);

#ifdef DEBUG
  std::cout << "Checking following program for monotonicity:" << endl;
  program.output(ns, "", std::cout);
#endif

  try {
    if (program.check_sat()) {
  #ifdef DEBUG
      std::cout << "Path is not monotone" << endl;
  #endif

      return false;
    }
  } catch (string s) {
    std::cout << "Error in monotonicity SAT check: " << s << endl;
     return false;
  } catch (const char *s) {
    std::cout << "Error in monotonicity SAT check: " << s << endl;
     return false;
  }

#ifdef DEBUG
  std::cout << "Path is monotone" << std::endl;
#endif

  return true;
}

void acceleration_utilst::ensure_no_overflows(scratch_programt &program) {
  symbolt overflow_sym = fresh_symbol("polynomial::overflow", bool_typet());
  const exprt &overflow_var = overflow_sym.symbol_expr();
  overflow_instrumentert instrumenter(program, overflow_var, symbol_table);

  optionst checker_options;

  checker_options.set_option("signed-overflow-check", true);
  checker_options.set_option("unsigned-overflow-check", true);
  checker_options.set_option("assert-to-assume", true);
  checker_options.set_option("assumptions", true);
  checker_options.set_option("simplify", true);


#ifdef DEBUG
  time_t now = time(0);
  std::cout << "Adding overflow checks at " << now << "..." << std::endl;
#endif

  instrumenter.add_overflow_checks();
  program.add_instruction(ASSUME)->guard = not_exprt(overflow_var);

  //goto_functionst::goto_functiont fn;
  //fn.body.instructions.swap(program.instructions);
  //goto_check(ns, checker_options, fn);
  //fn.body.instructions.swap(program.instructions);

#ifdef DEBUG
  now = time(0);
  std::cout << "Done at " << now << "." << std::endl;
#endif
}

acceleration_utilst::expr_pairst acceleration_utilst::gather_array_assignments(
    goto_programt::instructionst &loop_body,
    expr_sett &arrays_written) {
  expr_pairst assignments;

  for (goto_programt::instructionst::reverse_iterator r_it = loop_body.rbegin();
       r_it != loop_body.rend();
       ++r_it) {
    if (r_it->is_assign()) {
      // Is this an array assignment?
      code_assignt assignment = to_code_assign(r_it->code);

      if (assignment.lhs().id() == ID_index) {
        // This is an array assignment -- accumulate it in our list.
        assignments.push_back(make_pair(assignment.lhs(), assignment.rhs()));

        // Also add this array to the set of arrays written to.
        index_exprt index_expr = to_index_expr(assignment.lhs());
        arrays_written.insert(index_expr.array());
      } else {
        // This is a regular assignment.  Do weakest precondition on all our
        // array expressions with respect to this assignment.
        for (expr_pairst::iterator a_it = assignments.begin();
             a_it != assignments.end();
             ++a_it) {
          replace_expr(assignment.lhs(), assignment.rhs(), a_it->first);
          replace_expr(assignment.lhs(), assignment.rhs(), a_it->second);
        }
      }
    }
  }

  return assignments;
}

bool acceleration_utilst::do_arrays(goto_programt::instructionst &loop_body,
                                        map<exprt, polynomialt> &polynomials,
                                        exprt &loop_counter,
                                        substitutiont &substitution,
                                        scratch_programt &program) {
#ifdef DEBUG
  std::cout << "Doing arrays..." << endl;
#endif

  expr_sett arrays_written;
  expr_pairst array_assignments;
  
  array_assignments = gather_array_assignments(loop_body, arrays_written);

#ifdef DEBUG
  std::cout << "Found " << array_assignments.size() << " array assignments" << std::endl;
#endif

  if (array_assignments.size() == 0) {
    // The loop doesn't write to any arrays.  We're done!
    return true;
  }

  polynomial_array_assignmentst poly_assignments;
  polynomialst nondet_indices;

  if (!array_assignments2polys(array_assignments, polynomials, poly_assignments,
                               nondet_indices)) {
    // We weren't able to model some array assignment.  That means we need to
    // bail out altogether :-(
#ifdef DEBUG
    std::cout << "Couldn't model an array assignment :-(" << endl;
#endif
    return false;
  }

  // First make all written-to arrays nondeterministic.
  for (expr_sett::iterator it = arrays_written.begin();
       it != arrays_written.end();
       ++it) {
    program.assign(*it, side_effect_expr_nondett(it->type()));
  }

 // Now add in all the effects of this loop on the arrays.
  exprt::operandst array_operands;

  for (polynomial_array_assignmentst::iterator it = poly_assignments.begin();
       it != poly_assignments.end();
       ++it) {
    polynomialt stashed_index = it->index;
    polynomialt stashed_value = it->value;

    stashed_index.substitute(substitution);
    stashed_value.substitute(substitution);

    array_operands.push_back(equal_exprt(
            index_exprt(it->array, stashed_index.to_expr()),
            stashed_value.to_expr()));
  }

  exprt arrays_expr=conjunction(array_operands);

  symbolt k_sym = fresh_symbol("polynomial::k", unsignedbv_typet(POLY_WIDTH));
  exprt k = k_sym.symbol_expr();

  exprt k_bound = and_exprt(binary_relation_exprt(from_integer(0, k.type()), ID_le, k),
                            binary_relation_exprt(k, ID_lt, loop_counter));
  replace_expr(loop_counter, k, arrays_expr);

  implies_exprt implies(k_bound, arrays_expr);

  exprt forall(ID_forall);
  forall.type() = bool_typet();
  forall.copy_to_operands(k);
  forall.copy_to_operands(implies);

  program.assume(forall);

  // Now have to encode that the array doesn't change at indices we didn't
  // touch.
  for (expr_sett::iterator a_it = arrays_written.begin();
       a_it != arrays_written.end();
       ++a_it) {
    exprt array = *a_it;
    exprt old_array = substitution[array];
    vector<polynomialt> indices;
    bool nonlinear_index = false;

    for (polynomial_array_assignmentst::iterator it = poly_assignments.begin();
         it != poly_assignments.end();
         ++it) {
      if (it->array == array) {
        polynomialt index = it->index;
        index.substitute(substitution);
        indices.push_back(index);

        if (index.max_degree(loop_counter) > 1 ||
            (index.coeff(loop_counter) != 1 && index.coeff(loop_counter) != -1)) {
#ifdef DEBUG
          std::cout << expr2c(index.to_expr(), ns) << " is nonlinear" << endl;
#endif
          nonlinear_index = true;
        }
      }
    }

    exprt idx_never_touched = nil_exprt();
    symbolt idx_sym = fresh_symbol("polynomial::idx", signedbv_typet(POLY_WIDTH));
    exprt idx = idx_sym.symbol_expr();


    // Optimization: if all the assignments to a particular array A are of the
    // form:
    // A[loop_counter + e] = f
    // where e does not contain loop_counter, we don't need quantifier alternation
    // to encode the non-changedness.  We can get away with the expression:
    // forall k; k < e || k > loop_counter+e => A[k] = old_A[k]

    if (!nonlinear_index) {
      polynomialt pos_eliminator, neg_eliminator;

      neg_eliminator.from_expr(loop_counter);
      pos_eliminator = neg_eliminator;
      pos_eliminator.mult(-1);

      exprt::operandst unchanged_operands;

      for (vector<polynomialt>::iterator it = indices.begin();
           it != indices.end();
           ++it) {
        polynomialt index = *it;
        exprt max_idx, min_idx;

        if (index.coeff(loop_counter) == 1) {
          max_idx = minus_exprt(index.to_expr(), from_integer(1, index.to_expr().type()));
          index.add(pos_eliminator);
          min_idx = index.to_expr();
        } else if (index.coeff(loop_counter) == -1) {
          min_idx = plus_exprt(index.to_expr(), from_integer(1, index.to_expr().type()));
          index.add(neg_eliminator);
          max_idx = index.to_expr();
        } else {
          assert(!"ITSALLGONEWRONG");
        }

        or_exprt unchanged_by_this_one(
            binary_relation_exprt(idx, "<", min_idx),
            binary_relation_exprt(idx, ">", max_idx));
        unchanged_operands.push_back(unchanged_by_this_one);
      }

      idx_never_touched = conjunction(unchanged_operands);
    }
    else
    {
      // The vector `indices' now contains all of the indices written to for the
      // current array, each with the free variable loop_counter.  Now let's
      // build an expression saying that the fresh variable idx is none of these
      // indices.
      exprt::operandst idx_touched_operands;

      for (vector<polynomialt>::iterator it = indices.begin();
           it != indices.end();
           ++it) {
        idx_touched_operands.push_back(not_exprt(equal_exprt(idx, it->to_expr())));
      }

      exprt idx_not_touched=conjunction(idx_touched_operands);

      // OK, we have an expression saying idx is not touched by the
      // loop_counter'th iteration.  Let's quantify that to say that idx is not
      // touched at all.
      symbolt l_sym = fresh_symbol("polynomial::l", signedbv_typet(POLY_WIDTH));
      exprt l = l_sym.symbol_expr();

      replace_expr(loop_counter, l, idx_not_touched);

      // 0 < l <= loop_counter => idx_not_touched
      and_exprt l_bound(binary_relation_exprt(from_integer(0, l.type()), ID_lt, l),
                        binary_relation_exprt(l, ID_le, loop_counter));
      implies_exprt idx_not_touched_bound(l_bound, idx_not_touched);

      idx_never_touched = exprt(ID_forall);
      idx_never_touched.type() = bool_typet();
      idx_never_touched.copy_to_operands(l);
      idx_never_touched.copy_to_operands(idx_not_touched_bound);
    }

    // We now have an expression saying idx is never touched.  It is the
    // following:
    // forall l . 0 < l <= loop_counter => idx != index_1 && ... && idx != index_N
    //
    // Now let's build an expression saying that such an idx doesn't get
    // updated by this loop, i.e.
    // idx_never_touched => A[idx] == A_old[idx]
    equal_exprt value_unchanged(index_exprt(array, idx),
                                index_exprt(old_array, idx));
    implies_exprt idx_unchanged(idx_never_touched, value_unchanged);

    // Cool.  Finally, we want to quantify over idx to say that every idx that
    // is never touched has its value unchanged.  So our expression is:
    // forall idx . idx_never_touched => A[idx] == A_old[idx]
    exprt array_unchanged(ID_forall);
    array_unchanged.type() = bool_typet();
    array_unchanged.copy_to_operands(idx);
    array_unchanged.copy_to_operands(idx_unchanged);

    // And we're done!
    program.assume(array_unchanged);
  }

  return true;
}

bool acceleration_utilst::array_assignments2polys(
    expr_pairst &array_assignments,
    map<exprt, polynomialt> &polynomials,
    polynomial_array_assignmentst &array_polynomials,
    polynomialst &nondet_indices) {
  for (expr_pairst::iterator it = array_assignments.begin();
       it != array_assignments.end();
       ++it) {
    polynomial_array_assignmentt poly_assignment;
    index_exprt index_expr = to_index_expr(it->first);

    poly_assignment.array = index_expr.array();

    if (!expr2poly(index_expr.index(), polynomials, poly_assignment.index)) {
      // Couldn't convert the index -- bail out.
#ifdef DEBUG
      std::cout << "Couldn't convert index: " << expr2c(index_expr.index(), ns) << endl;
#endif
      return false;
    }

#ifdef DEBUG
    std::cout << "Converted index to: " << expr2c(poly_assignment.index.to_expr(), ns)
        << endl;
#endif

    if (it->second.id() == ID_nondet) {
      nondet_indices.push_back(poly_assignment.index);
    } else if (!expr2poly(it->second, polynomials, poly_assignment.value)) {
      // Couldn't conver the RHS -- bail out.
#ifdef DEBUG
      std::cout << "Couldn't convert RHS: " << expr2c(it->second, ns) << endl;
#endif
      return false;
    } else {
#ifdef DEBUG
      std::cout << "Converted RHS to: " << expr2c(poly_assignment.value.to_expr(), ns)
          << endl;
#endif

      array_polynomials.push_back(poly_assignment);
    }
  }

  return true;
}

bool acceleration_utilst::expr2poly(exprt &expr,
                                        map<exprt, polynomialt> &polynomials,
                                        polynomialt &poly) {
  exprt subbed_expr = expr;

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    replace_expr(it->first, it->second.to_expr(), subbed_expr);
  }

#ifdef DEBUG
  std::cout << "expr2poly(" << expr2c(subbed_expr, ns) << ")" << endl;
#endif

  try {
    poly.from_expr(subbed_expr);
  } catch (...) {
    return false;
  }

  return true;
}

bool acceleration_utilst::do_nonrecursive(goto_programt::instructionst &body,
                                          map<exprt, polynomialt> &polynomials,
                                          exprt &loop_counter,
                                          substitutiont &substitution,
                                          expr_sett &nonrecursive,
                                          scratch_programt &program) {
  // We have some variables that are defined non-recursively -- that is to say,
  // their value at the end of a loop iteration does not depend on their value
  // at the previous iteration.  We can solve for these variables by just forward
  // simulating the path and taking the expressions we get at the end.
  replace_mapt state;
  expr_sett array_writes;
  expr_sett arrays_written;
  expr_sett arrays_read;

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    const exprt &var = it->first;
    polynomialt poly = it->second;
    poly.substitute(substitution);
    exprt e = poly.to_expr();

#if 0
    replace_expr(loop_counter,
                 minus_exprt(loop_counter, from_integer(1, loop_counter.type())),
                 e);
#endif

    state[var] = e;
  }

  for (expr_sett::iterator it = nonrecursive.begin();
       it != nonrecursive.end();
       ++it) {
    exprt e = *it;
    state[e] = e;
  }

  for (goto_programt::instructionst::iterator it = body.begin();
       it != body.end();
       ++it) {
    if (it->is_assign()) {
      exprt lhs = it->code.op0();
      exprt rhs = it->code.op1();

      if (lhs.id() == ID_dereference) {
        // Not handling pointer dereferences yet...
#ifdef DEBUG
        std::cout << "Bailing out on write-through-pointer" << std::endl;
#endif
        return false;
      }

      if (lhs.id() == ID_index) {
        replace_expr(state, lhs.op1());
        array_writes.insert(lhs);

        if (arrays_written.find(lhs.op0()) != arrays_written.end()) {
          // We've written to this array before -- be conservative and bail
          // out now.
#ifdef DEBUG
          std::cout << "Bailing out on array written to twice in loop: " <<
            expr2c(lhs.op0(), ns) << std::endl;
#endif
          return false;
        }

        arrays_written.insert(lhs.op0());
      }

      replace_expr(state, rhs);
      state[lhs] = rhs;

      gather_array_accesses(rhs, arrays_read);
    }
  }

  // Be conservative: if we read and write from the same array, bail out.
  for (expr_sett::iterator it = arrays_written.begin();
       it != arrays_written.end();
       ++it) {
    if (arrays_read.find(*it) != arrays_read.end()) {
#ifdef DEBUG
      std::cout << "Bailing out on array read and written on same path" << std::endl;
#endif
      return false;
    }
  }

  for (expr_sett::iterator it = nonrecursive.begin();
       it != nonrecursive.end();
       ++it) {
    if (it->id() == ID_symbol) {
      exprt &val = state[*it];
      program.assign(*it, val);

#ifdef DEBUG
      std::cout << "Fitted nonrecursive: " << expr2c(*it, ns) << " = " <<
        expr2c(val, ns) << std::endl;
#endif
    }
  }

  for (expr_sett::iterator it = array_writes.begin();
       it != array_writes.end();
       ++it) {
    const exprt &lhs = *it;
    const exprt &rhs = state[*it];

    if (!assign_array(lhs, rhs, loop_counter, program)) {
#ifdef DEBUG
      std::cout << "Failed to assign a nonrecursive array: " <<
        expr2c(lhs, ns) << " = " << expr2c(rhs, ns) << std::endl;
#endif
      return false;
    }
  }

  return true;
}

bool acceleration_utilst::assign_array(const exprt &lhs,
                                       const exprt &rhs,
                                       const exprt &loop_counter,
                                       scratch_programt &program) {
#ifdef DEBUG
  std::cout << "Modelling array assignment " << expr2c(lhs, ns) << " = " <<
    expr2c(rhs, ns) << std::endl;
#endif

  if (lhs.id() == ID_dereference) {
    // Don't handle writes through pointers for now...
#ifdef DEBUG
    std::cout << "Bailing out on write-through-pointer" << std::endl;
#endif
    return false;
  }

  // We handle N iterations of the array write:
  //
  //  A[i] = e
  //
  // by the following sequence:
  //
  //  A' = nondet()
  //  assume(forall 0 <= k < N . A'[i(k/loop_counter)] = e(k/loop_counter));
  //  assume(forall j . notwritten(j) ==> A'[j] = A[j]);
  //  A = A'

  const exprt &arr = lhs.op0();
  exprt idx = lhs.op1();
  const exprt &fresh_array =
    fresh_symbol("polynomial::array", arr.type()).symbol_expr();

  // First make the fresh nondet array.
  program.assign(fresh_array, side_effect_expr_nondett(arr.type()));

  // Then assume that the fresh array has the appropriate values at the indices
  // the loop updated.
  exprt changed = equal_exprt(lhs, rhs);
  replace_expr(arr, fresh_array, changed);

  symbolt k_sym = fresh_symbol("polynomial::k", unsignedbv_typet(POLY_WIDTH));
  exprt k = k_sym.symbol_expr();

  exprt k_bound = and_exprt(binary_relation_exprt(from_integer(0, k.type()), ID_le, k),
                            binary_relation_exprt(k, ID_lt, loop_counter));
  replace_expr(loop_counter, k, changed);

  implies_exprt implies(k_bound, changed);

  exprt forall(ID_forall);
  forall.type() = bool_typet();
  forall.copy_to_operands(k);
  forall.copy_to_operands(implies);

  program.assume(forall);

  // Now let's ensure that the array did not change at the indices we didn't touch.
#ifdef DEBUG
  std::cout << "Trying to polynomialize " << expr2c(idx, ns) << std::endl;
#endif

  polynomialt poly;

  try {
    if (idx.id() == ID_pointer_offset) {
      poly.from_expr(idx.op0());
    } else {
      poly.from_expr(idx);
    }
  } catch(...) {
    // idx is probably nonlinear... bail out.
#ifdef DEBUG
    std::cout << "Failed to polynomialize" << std::endl;
#endif
    return false;
  }

  if (poly.max_degree(loop_counter) > 1) {
    // The index expression is nonlinear, e.g. it's something like:
    //
    //  A[x*loop_counter] = 0;
    //
    // where x changes inside the loop.  Modelling this requires quantifier
    // alternation, and that's too expensive.  Bail out.
#ifdef DEBUG
    std::cout << "Bailing out on nonlinear index: " << expr2c(idx, ns) << std::endl;
#endif
    return false;
  }

  int stride = poly.coeff(loop_counter);
  exprt not_touched;
  exprt lower_bound = idx;
  exprt upper_bound = idx;

  if (stride > 0) {
    replace_expr(loop_counter, from_integer(0, loop_counter.type()), lower_bound);
    simplify_expr(lower_bound, ns);
  } else {
    replace_expr(loop_counter, from_integer(0, loop_counter.type()), upper_bound);
    simplify_expr(upper_bound, ns);
  }

  if (stride == 0) {
    // The index we write to doesn't depend on the loop counter....
    // We could optimise for this, but I suspect it's not going to happen to much
    // so just bail out.
#ifdef DEBUG
    std::cout << "Bailing out on write to constant array index: " <<
      expr2c(idx, ns) << std::endl;
#endif
    return false;
  } else if (stride == 1 || stride == -1) {
    // This is the simplest case -- we have an assignment like:
    //
    //  A[c + loop_counter] = e;
    //
    // where c doesn't change in the loop.  The expression to say it doesn't
    // change at unexpected places is:
    //
    //  forall k . (k < c || k >= loop_counter + c) ==> A'[k] == A[k]

    not_touched = or_exprt(
        binary_relation_exprt(k, "<", lower_bound),
        binary_relation_exprt(k, ">=", upper_bound));
  } else {
    // A more complex case -- our assignment is:
    //
    //  A[c + s*loop_counter] = e;
    //
    // where c and s are constants.  Now our condition for an index i to be unchanged is:
    //
    //  i < c || i >= (c + s*loop_counter) || (i - c) % s != 0

    exprt step = minus_exprt(k, lower_bound);

    not_touched = or_exprt(
        or_exprt(
          binary_relation_exprt(k, "<", lower_bound),
          binary_relation_exprt(k, ">=", lower_bound)),
          notequal_exprt(mod_exprt(step, from_integer(stride, step.type())),
                         from_integer(0, step.type())));
  }

  // OK now do the assumption.
  exprt fresh_lhs = lhs;
  exprt old_lhs = lhs;

  replace_expr(arr, fresh_array, fresh_lhs);
  replace_expr(loop_counter, k, fresh_lhs);

  replace_expr(loop_counter, k, old_lhs);

  equal_exprt idx_unchanged(fresh_lhs, old_lhs);

  implies = implies_exprt(not_touched, idx_unchanged);

  forall = exprt(ID_forall);
  forall.type() = bool_typet();
  forall.copy_to_operands(k);
  forall.copy_to_operands(implies);

  program.assume(forall);

  // Finally, assign the array to the fresh one we've just build.
  program.assign(arr, fresh_array);

  return true;
}

void acceleration_utilst::gather_array_accesses(const exprt &e, expr_sett &arrays) {
  if (e.id() == ID_index ||
      e.id() == ID_dereference) {
    arrays.insert(e.op0());
  }

  forall_operands(it, e) {
    gather_array_accesses(*it, arrays);
  }
}

void acceleration_utilst::extract_polynomial(scratch_programt &program,
                                                 set<pair<expr_listt, exprt> >
                                                   &coefficients,
                                                 polynomialt &polynomial) {
  for (set<pair<expr_listt, exprt> >::iterator it = coefficients.begin();
       it != coefficients.end();
       ++it) {
    monomialt monomial;
    expr_listt terms = it->first;
    exprt coefficient = it->second;
    constant_exprt concrete_term = to_constant_expr(program.eval(coefficient));
    map<exprt, int> degrees;

    mp_integer mp = binary2integer(concrete_term.get_value().c_str(), true);
    monomial.coeff = mp.to_long();

    if (monomial.coeff == 0) {
      continue;
    }

    for (expr_listt::iterator it = terms.begin();
         it != terms.end();
         ++it) {
      exprt term = *it;

      if (degrees.find(term) != degrees.end()) {
        degrees[term]++;
      } else {
        degrees[term] = 1;
      }
    }

    for (map<exprt, int>::iterator it = degrees.begin();
         it != degrees.end();
         ++it) {
      monomialt::termt term;
      term.var = it->first;
      term.exp = it->second;
      monomial.terms.push_back(term);
    }

    polynomial.monomials.push_back(monomial);
  }
}

symbolt acceleration_utilst::fresh_symbol(string base, typet type)
{
  static int num_symbols = 0;

  string name = base + "_" + i2string(num_symbols++);
  symbolt ret;
  ret.module = "scratch";
  ret.name = name;
  ret.base_name = name;
  ret.pretty_name = name;
  ret.type = type;

  symbol_table.add(ret);

  return ret;
}


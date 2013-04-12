#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sstream>

#include <goto-programs/goto_program.h>
#include <goto-programs/wp.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <analyses/goto_check.h>

#include <ansi-c/expr2c.h>

#include <symbol_table.h>
#include <options.h>
#include <std_expr.h>
#include <std_code.h>
#include <i2string.h>
#include <find_symbols.h>
#include <rename.h>
#include <simplify_expr.h>
#include <replace_expr.h>
#include <arith_tools.h>

#include "polynomial_accelerator.h"
#include "util.h"

#define DEBUG


bool polynomial_acceleratort::accelerate(patht &loop, goto_programt &accelerator) {
  goto_programt::instructionst body;

  for (patht::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    body.push_back(*(it->loc));
  }

  set<exprt> targets = find_modified(body);
  map<exprt, polynomialt> polynomials;
  scratch_programt program(symbol_table);
  goto_programt::instructionst assigns;

#ifdef DEBUG
  std::cout << "Polynomial accelerating program:" << endl;

  for (goto_programt::instructionst::iterator it = body.begin();
       it != body.end();
       ++it) {
    program.output_instruction(ns, "scratch", std::cout, it);
  }

  std::cout << "Modified:" << endl;

  for (set<exprt>::iterator it = targets.begin();
       it != targets.end();
       ++it) {
    std::cout << expr2c(*it, ns) << endl;
  }
#endif

  for (goto_programt::instructionst::iterator it = body.begin();
       it != body.end();
       ++it) {
    if (it->is_assign() || it->is_decl()) {
      assigns.push_back(*it);
    }
  }

  if (loop_counter.is_nil()) {
    symbolt loop_sym = program.fresh_symbol("polynomial::loop_counter");
    symbol_table.add(loop_sym);
    loop_counter = loop_sym.symbol_expr();
  }

  for (set<exprt>::iterator it = targets.begin();
       it != targets.end();
       ++it) {
    polynomialt poly;
    exprt target = *it;

    if (target.id() == ID_index) {
      // We'll handle this later.
      continue;
    }

    if (fit_polynomial(assigns, target, poly)) {
      map<exprt, polynomialt> this_poly;
      this_poly[target] = poly;

      if (check_inductive(this_poly, assigns)) {
        polynomials.insert(make_pair(target, poly));
      }
    }
  }

  if (polynomials.empty()) {
    return false;
  }

  /*
  if (!check_inductive(polynomials, assigns)) {
    // They're not inductive :-(
    return false;
  }
  */

  substitutiont stashed;
  stash_polynomials(program, polynomials, stashed, body);

  exprt guard;
  bool path_is_monotone;
  
  try {
    path_is_monotone = do_assumptions(polynomials, loop, guard);
  } catch (string s) {
    // Couldn't do WP.
    std::cout << "Assumptions error: " << s << endl;
    return false;
  }

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    replace_expr(it->first, it->second.to_expr(), guard);
  }

  if (path_is_monotone) {
    // OK cool -- the path is monotone, so we can just assume the condition for
    // the last iteration.
    replace_expr(loop_counter,
                 minus_exprt(loop_counter, from_integer(1, loop_counter.type())),
                 guard);
  } else {
    // The path is not monotone, so we need to introduce a quantifier to ensure
    // that the condition held for all 0 <= k < n.
    symbolt k_sym = program.fresh_symbol("polynomial::k");
    symbol_table.add(k_sym);
    exprt k = k_sym.symbol_expr();

    exprt k_bound = and_exprt(binary_relation_exprt(from_integer(0, k.type()), "<=", k),
                              binary_relation_exprt(k, "<", loop_counter));
    replace_expr(loop_counter, k, guard);

    simplify(guard, ns);

    implies_exprt implies(k_bound, guard);

    exprt forall(ID_forall);
    forall.type() = bool_typet();
    forall.copy_to_operands(k);
    forall.copy_to_operands(implies);

    guard = forall;
  }

  // All our conditions are met -- we can finally build the accelerator!
  // It is of the form:
  //
  // loop_counter = *;
  // target1 = polynomial1;
  // target2 = polynomial2;
  // ...
  // assume(guard);
  // assume(no overflows in previous code);

  program.assign(loop_counter, nondet_exprt(loop_counter.type()));
  //program.assume(binary_relation_exprt(loop_counter, ">", make_constant(0)));
  program.assume(binary_relation_exprt(loop_counter, ">", from_integer(0, signedbv_typet(32))));

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    program.assign(it->first, it->second.to_expr());
  }

  // Add in any array assignments we can do now.
  if (!do_arrays(assigns, polynomials, loop_counter, stashed, program)) {
    // We couldn't model some of the array assignments with polynomials...
    // Unfortunately that means we just have to bail out.
    return false;
  }


  program.add_instruction(ASSUME)->guard = guard;
  program.fix_types();

  if (path_is_monotone) {
    ensure_no_overflows(program);
  }

  accelerator.instructions = program.instructions;

  return true;
}

bool polynomial_acceleratort::fit_polynomial(goto_programt::instructionst &body,
                                             exprt &var,
                                             polynomialt &polynomial) {
  // These are the variables that var depends on with respect to the body.
  set<exprt> influence = cone_of_influence(body, var);
  vector<expr_listt> parameters;
  set<pair<expr_listt, exprt> > coefficients;
  expr_listt exprs;
  scratch_programt program(symbol_table);

#ifdef DEBUG
  std::cout << "Fitting a polynomial for " << expr2c(var, ns) << ", which depends on:"
       << endl;

  for (set<exprt>::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    std::cout << expr2c(*it, ns) << endl;
  }
#endif

  for (set<exprt>::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    exprs.clear();

    exprs.push_back(*it);
    parameters.push_back(exprs);

    exprs.push_back(loop_counter);
    parameters.push_back(exprs);
  }

  // N
  exprs.clear();
  exprs.push_back(loop_counter);
  parameters.push_back(exprs);

  // N^2
  exprs.push_back(loop_counter);
  //parameters.push_back(exprs);

  // Constant
  exprs.clear();
  parameters.push_back(exprs);

  for (vector<expr_listt>::iterator it = parameters.begin();
       it != parameters.end();
       ++it) {
    symbolt coeff = program.fresh_symbol("polynomial::coeff");
    symbol_table.add(coeff);
    coefficients.insert(make_pair(*it, coeff.symbol_expr()));
  }

  // Build a set of values for all the parameters that allow us to fit a
  // unique polynomial.

  // XXX
  // This isn't ok -- we're assuming 0, 1 and 2 are valid values for the
  // variables involved, but this might make the path condition UNSAT.  Should
  // really be solving the path constraints a few times to get valid probe
  // values...

  map<exprt, int> values;

  for (set<exprt>::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    values[*it] = 0;
  }

  for (int n = 0; n <= 2; n++) {
    for (set<exprt>::iterator it = influence.begin();
         it != influence.end();
         ++it) {
      values[*it] = 1;
      assert_for_values(program, values, coefficients, n, body, var);
      values[*it] = 0;
    }
  }

  // Now just need to assert the case where all values are 0 and all are 2.
  assert_for_values(program, values, coefficients, 0, body, var);
  assert_for_values(program, values, coefficients, 2, body, var);

  for (set<exprt>::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    values[*it] = 2;
  }

  assert_for_values(program, values, coefficients, 2, body, var);

  // Now do an ASSERT(false) to grab a counterexample
  goto_programt::targett assertion = program.add_instruction(ASSERT);
  assertion->guard = false_exprt();

  //ensure_no_overflows(program);

#ifdef DEBUG
  std::cout << "Fitting polynomial with program:" << endl;
  program.output(std::cout);
#endif

  // If the path is satisfiable, we've fitted a polynomial.  Extract the
  // relevant coefficients and return the expression.
  try {
    if (program.check_sat()) {
      extract_polynomial(program, coefficients, polynomial);
      return true;
    }
  } catch (string s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  } catch (const char *s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  }

  return false;
}

void polynomial_acceleratort::assert_for_values(scratch_programt &program,
                                                map<exprt, int> &values,
                                                set<pair<expr_listt, exprt> >
                                                   &coefficients,
                                                int num_unwindings,
                                                goto_programt::instructionst
                                                   &loop_body,
                                                exprt &target) {
  // First set the initial values of the all the variables...
  for (map<exprt, int>::iterator it = values.begin();
       it != values.end();
       ++it) {
    program.assign(it->first, from_integer(it->second, it->first.type()));
  }

  // Now unwind the loop as many times as we need to.
  for (int i = 0; i < num_unwindings; i++) {
    program.append(loop_body);
  }

  // Now build the polynomial for this point and assert it fits.
  exprt rhs = nil_exprt();

  for (set<pair<expr_listt, exprt> >::iterator it = coefficients.begin();
       it != coefficients.end();
       ++it) {
    int concrete_value = 1;

    for (expr_listt::const_iterator e_it = it->first.begin();
         e_it != it->first.end();
         ++e_it) {
      exprt e = *e_it;

      if (e == loop_counter) {
        concrete_value *= num_unwindings;
      } else {
        map<exprt, int>::iterator v_it = values.find(e);

        assert(v_it != values.end());

        concrete_value *= v_it->second;
      }
    }

    // OK, concrete_value now contains the value of all the relevant variables
    // multiplied together.  Create the term concrete_value*coefficient and add
    // it into the polynomial.
    exprt term = mult_exprt(from_integer(concrete_value, it->second.type()), it->second);

    if (rhs.is_nil()) {
      rhs = term;
    } else {
      rhs = plus_exprt(rhs, term);
    }
  }

  // We now have the RHS of the polynomial.  Assert that this is equal to the
  // actual value of the variable we're fitting.
  exprt polynomial_holds = equal_exprt(target, rhs);

  // Finally, assert that the polynomial equals the variable we're fitting.
  goto_programt::targett assumption = program.add_instruction(ASSUME);
  assumption->guard = polynomial_holds;
}

void polynomial_acceleratort::extract_polynomial(scratch_programt &program,
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

void gather_rvalues(const exprt &expr, set<exprt> &rvalues) {
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

set<exprt> polynomial_acceleratort::cone_of_influence(goto_programt::instructionst
                                                        &body,
                                                      exprt &target) {
  set<exprt> cone;

  gather_rvalues(target, cone);

  for (goto_programt::instructionst::reverse_iterator r_it = body.rbegin();
       r_it != body.rend();
       ++r_it) {
    if (r_it->is_assign()) {
      // XXX -- this doesn't work if the assignment is not to a symbol, e.g.
      // A[i] = 0;
      // or
      // *p = x;
      code_assignt assignment = to_code_assign(r_it->code);
      set<exprt> lhs_syms;

      gather_rvalues(assignment.lhs(), lhs_syms);

      for (set<exprt>::iterator s_it = lhs_syms.begin();
           s_it != lhs_syms.end();
           ++s_it) {
        if (cone.find(*s_it) != cone.end()) {
          // We're assigning to something in the cone of influence -- expand the
          // cone.
          gather_rvalues(assignment.rhs(), cone);
          break;
        }
      }
    }
  }

  return cone;
}

set<exprt> find_modified(goto_programt::instructionst &body) {
  set<exprt> ret;

  for (goto_programt::instructionst::iterator it = body.begin();
       it != body.end();
       ++it) {
    if (it->is_assign()) {
      code_assignt assignment = to_code_assign(it->code);
      ret.insert(assignment.lhs());
    }
  }

  return ret;
}

bool polynomial_acceleratort::check_inductive(map<exprt, polynomialt> polynomials,
                                              goto_programt::instructionst &body) {
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

  stash_polynomials(program, polynomials, substitution, body);
 
  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    exprt holds = equal_exprt(it->first, it->second.to_expr());
    program.add_instruction(ASSUME)->guard = holds;

    polynomials_hold.push_back(holds);
  }

  program.append(body);

  codet inc_loop_counter = code_assignt(loop_counter,
                                        plus_exprt(loop_counter, from_integer(1, loop_counter.type())));
  program.add_instruction(ASSIGN)->code = inc_loop_counter;

  for (vector<exprt>::iterator it = polynomials_hold.begin();
       it != polynomials_hold.end();
       ++it) {
    program.add_instruction(ASSERT)->guard = *it;
  }

#ifdef DEBUG
  std::cout << "Checking following program for inductiveness:" << endl;
  program.output(std::cout);
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

void polynomial_acceleratort::stash_polynomials(
    scratch_programt &program,
    map<exprt, polynomialt> &polynomials,
    substitutiont &substitution,
    goto_programt::instructionst &body) {

  set<exprt> modified = find_modified(body);
  stash_variables(program, modified, substitution);

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    it->second.substitute(substitution);
  }
}

void polynomial_acceleratort::stash_variables(scratch_programt &program,
                                              set<exprt> modified,
                                              substitutiont &substitution) {
  find_symbols_sett vars;

  for (set<exprt>::iterator it = modified.begin();
       it != modified.end();
       ++it) {
    find_symbols(*it, vars);
  }

  irep_idt loop_counter_name = to_symbol_expr(loop_counter).get_identifier();
  vars.erase(loop_counter_name);

  for (find_symbols_sett::iterator it = vars.begin();
       it != vars.end();
       ++it) {
    symbolt stashed_sym = program.fresh_symbol("polynomial::stash");
    symbolt orig = symbol_table.lookup(*it);
    irep_idt stashed_name = stashed_sym.name;
    irep_idt orig_name = *it;

    stashed_sym.type = orig.type;
    symbol_table.add(stashed_sym);

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

exprt polynomial_acceleratort::precondition(patht &path) {
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

      if (lhs.id() == ID_symbol) {
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

  simplify(ret, ns);

  return ret;
}

bool polynomial_acceleratort::do_assumptions(map<exprt, polynomialt> polynomials,
                                             patht &loop,
                                             exprt &guard) {
  exprt condition = precondition(loop);

  goto_programt::instructionst body;

  for (patht::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    body.push_back(*it->loc);
  }

  scratch_programt program(symbol_table);

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
  // assume(target1 == polynomial1);
  // assume(target2 == polynomial2);
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

  substitutiont substitution;
  stash_polynomials(program, polynomials, substitution, body);

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

  program.assign(loop_counter, nondet_exprt(loop_counter.type()));

  for (vector<exprt>::iterator it = polynomials_hold.begin();
       it != polynomials_hold.end();
       ++it) {
    program.assume(*it);
  }

  program.assume(condition);
  program.assign(loop_counter,
                 plus_exprt(loop_counter, from_integer(1, loop_counter.type())));

  for (map<exprt, polynomialt>::iterator p_it = polynomials.begin();
       p_it != polynomials.end();
       ++p_it) {
    program.assign(p_it->first, p_it->second.to_expr());
  }

  program.add_instruction(ASSERT)->guard = condition;

  guard = not_exprt(condition);

  ensure_no_overflows(program);

#ifdef DEBUG
  std::cout << "Checking following program for monotonicity:" << endl;
  program.output(std::cout);
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

  return true;
}

void polynomial_acceleratort::ensure_no_overflows(goto_programt &program) {
  optionst checker_options;

  checker_options.set_option("signed-overflow-check", true);
  checker_options.set_option("unsigned-overflow-check", true);
  checker_options.set_option("assert-to-assume", true);
  checker_options.set_option("assumptions", true);
  checker_options.set_option("simplify", true);

  //goto_check(ns, checker_options, goto_functions);
}

polynomial_acceleratort::expr_pairst polynomial_acceleratort::gather_array_assignments(
    goto_programt::instructionst &loop_body,
    set<exprt> &arrays_written) {
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

bool polynomial_acceleratort::do_arrays(goto_programt::instructionst &loop_body,
                                        map<exprt, polynomialt> &polynomials,
                                        exprt &loop_counter,
                                        substitutiont &substitution,
                                        scratch_programt &program) {
#ifdef DEBUG
  std::cout << "Doing arrays..." << endl;
#endif

  set<exprt> arrays_written;
  expr_pairst array_assignments;
  
  array_assignments = gather_array_assignments(loop_body, arrays_written);

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
  for (set<exprt>::iterator it = arrays_written.begin();
       it != arrays_written.end();
       ++it) {
    program.assign(*it, nondet_exprt(it->type()));
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

  and_exprt arrays_expr(array_operands);

  symbolt k_sym = program.fresh_symbol("polynomial::k");
  symbol_table.add(k_sym);
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
  for (set<exprt>::iterator a_it = arrays_written.begin();
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
    symbolt idx_sym = program.fresh_symbol("polynomial::idx");
    symbol_table.add(idx_sym);
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

      idx_never_touched = and_exprt(unchanged_operands);
    } else {
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

      and_exprt idx_not_touched(idx_touched_operands);

      // OK, we have an expression saying idx is not touched by the
      // loop_counter'th iteration.  Let's quantify that to say that idx is not
      // touched at all.
      symbolt l_sym = program.fresh_symbol("polynomial::l");
      symbol_table.add(l_sym);
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

bool polynomial_acceleratort::array_assignments2polys(
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

bool polynomial_acceleratort::expr2poly(exprt &expr,
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

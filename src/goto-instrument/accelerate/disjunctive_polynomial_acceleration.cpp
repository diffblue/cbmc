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

#include "disjunctive_polynomial_acceleration.h"
#include "polynomial_accelerator.h"
#include "accelerator.h"
#include "util.h"
#include "cone_of_influence.h"
#include "overflow_instrumenter.h"

//#define DEBUG


bool disjunctive_polynomial_accelerationt::accelerate(
    path_acceleratort &accelerator) {
  map<exprt, polynomialt> polynomials;
  scratch_programt program(symbol_table);

#ifdef DEBUG
  std::cout << "Polynomial accelerating program:" << endl;

  for (goto_programt::instructionst::iterator it = goto_program.instructions.begin();
       it != goto_program.instructions.end();
       ++it) {
    if (loop.find(it) != loop.end()) {
      goto_program.output_instruction(ns, "scratch", std::cout, it);
    }
  }

  std::cout << "Modified:" << endl;

  for (expr_sett::iterator it = modified.begin();
       it != modified.end();
       ++it) {
    std::cout << expr2c(*it, ns) << endl;
  }
#endif

  if (loop_counter.is_nil()) {
    symbolt loop_sym = program.fresh_symbol("polynomial::loop_counter",
        unsignedbv_typet(32));
    symbol_table.add(loop_sym);
    loop_counter = loop_sym.symbol_expr();
  }

  patht &path = accelerator.path;
  path.clear();

  for (expr_sett::iterator it = modified.begin();
       it != modified.end();
       ++it) {
    polynomialt poly;
    exprt target = *it;

    if (it->type().id() == ID_bool) {
      // Hack: don't try to accelerate booleans.
      continue;
    }

    if (target.id() == ID_index) {
      // We'll handle this later.
      continue;
    }

    if (fit_polynomial(target, poly, path)) {
      map<exprt, polynomialt> this_poly;
      this_poly[target] = poly;

      if (check_inductive(this_poly, path)) {
#ifdef DEBUG
        std::cout << "Fitted a polynomial for " << expr2c(target, ns) <<
          std::endl;
#endif
        polynomials[target] = poly;
        accelerator.changed_vars.insert(target);
        break;
      }
    }
  }

  if (polynomials.empty()) {
    return false;
  }

  // Fit polynomials for the other variables.
  expr_sett dirty;
  find_modified(accelerator.path, dirty);
  polynomial_acceleratort path_acceleration(symbol_table, goto_functions,
      loop_counter);
  goto_programt::instructionst assigns;

  for (patht::iterator it = accelerator.path.begin();
       it != accelerator.path.end();
       ++it) {
    if (it->loc->is_assign() || it->loc->is_decl()) {
      assigns.push_back(*(it->loc));
    }
  }

  for (expr_sett::iterator it = dirty.begin();
       it != dirty.end();
       ++it) {
    if (it->type().id() == ID_bool) {
      // Hack: don't try to accelerate booleans.
      continue;
    }

    if (accelerator.changed_vars.find(*it) != accelerator.changed_vars.end()) {
      // We've accelerated variable this already.
      continue;
    }

    polynomialt poly;
    exprt target(*it);

    if (path_acceleration.fit_polynomial(assigns, target, poly)) {
      map<exprt, polynomialt> this_poly;
      this_poly[target] = poly;

      if (check_inductive(this_poly, accelerator.path)) {
        polynomials[target] = poly;
        accelerator.changed_vars.insert(target);
        continue;
      }
    }

    // We weren't able to accelerate this target...
    accelerator.dirty_vars.insert(target);
  }


  /*
  if (!check_inductive(polynomials, assigns)) {
    // They're not inductive :-(
    return false;
  }
  */

  substitutiont stashed;
  stash_polynomials(program, polynomials, stashed, path);

  exprt guard;
  bool path_is_monotone;
  
  try {
    path_is_monotone = do_assumptions(polynomials, path, guard);
  } catch (string s) {
    // Couldn't do WP.
    std::cout << "Assumptions error: " << s << endl;
    return false;
  }

  exprt pre_guard(guard);

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
    symbolt k_sym = program.fresh_symbol("polynomial::k",
        unsignedbv_typet(32));
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

  program.add_instruction(ASSUME)->guard = pre_guard;
  program.assign(loop_counter, side_effect_expr_nondett(loop_counter.type()));

  for (map<exprt, polynomialt>::iterator it = polynomials.begin();
       it != polynomials.end();
       ++it) {
    program.assign(it->first, it->second.to_expr());
    accelerator.changed_vars.insert(it->first);
  }

#if 0
  // Add in any array assignments we can do now.
  if (!do_arrays(assigns, polynomials, loop_counter, stashed, program)) {
    // We couldn't model some of the array assignments with polynomials...
    // Unfortunately that means we just have to bail out.
    return false;
  }
#endif

  program.add_instruction(ASSUME)->guard = guard;
  program.fix_types();

  if (path_is_monotone) {
    ensure_no_overflows(program);
  }

  accelerator.pure_accelerator.instructions.swap(program.instructions);

  return true;
}

bool disjunctive_polynomial_accelerationt::fit_polynomial(
                                             exprt &var,
                                             polynomialt &polynomial,
                                             patht &path) {
  // These are the variables that var depends on with respect to the body.
  vector<expr_listt> parameters;
  set<pair<expr_listt, exprt> > coefficients;
  expr_listt exprs;
  scratch_programt program(symbol_table);
  expr_sett influence;

  cone_of_influence(var, influence);

#ifdef DEBUG
  std::cout << "Fitting a polynomial for " << expr2c(var, ns) << ", which depends on:"
       << endl;

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    std::cout << expr2c(*it, ns) << endl;
  }
#endif

  for (expr_sett::iterator it = influence.begin();
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
  parameters.push_back(exprs);

  // Constant
  exprs.clear();
  parameters.push_back(exprs);

  for (vector<expr_listt>::iterator it = parameters.begin();
       it != parameters.end();
       ++it) {
    symbolt coeff = program.fresh_symbol("polynomial::coeff",
        signedbv_typet(32));
    symbol_table.add(coeff);
    coefficients.insert(make_pair(*it, coeff.symbol_expr()));

    // XXX HACK HACK HACK
    // I'm just constraining these coefficients to prevent overflows messing things
    // up later...  Should really do this properly somehow.
    program.assume(binary_relation_exprt(from_integer(-(1 << 10), signedbv_typet(32)),
            "<", coeff.symbol_expr()));
    program.assume(binary_relation_exprt(coeff.symbol_expr(), "<",
        from_integer(1 << 10, signedbv_typet(32))));
  }

  // Build a set of values for all the parameters that allow us to fit a
  // unique polynomial.

  map<exprt, exprt> ivals1;
  map<exprt, exprt> ivals2;
  map<exprt, exprt> ivals3;

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    symbolt ival1 = program.fresh_symbol("polynomial::init",
        it->type());
    symbolt ival2 = program.fresh_symbol("polynomial::init",
        it->type());
    symbolt ival3 = program.fresh_symbol("polynomial::init",
        it->type());

    program.assume(binary_relation_exprt(ival1.symbol_expr(), "<",
          ival2.symbol_expr()));
    program.assume(binary_relation_exprt(ival2.symbol_expr(), "<",
          ival3.symbol_expr()));

    if (it->type() == signedbv_typet()) {
      program.assume(binary_relation_exprt(ival1.symbol_expr(), ">",
            from_integer(-100, it->type())));
    }
    program.assume(binary_relation_exprt(ival1.symbol_expr(), "<",
          from_integer(100, it->type())));

    if (it->type() == signedbv_typet()) {
      program.assume(binary_relation_exprt(ival2.symbol_expr(), ">",
            from_integer(-100, it->type())));
    }
    program.assume(binary_relation_exprt(ival2.symbol_expr(), "<",
          from_integer(100, it->type())));

    if (it->type() == signedbv_typet()) {
      program.assume(binary_relation_exprt(ival3.symbol_expr(), ">",
            from_integer(-100, it->type())));
    }
    program.assume(binary_relation_exprt(ival3.symbol_expr(), "<",
          from_integer(100, it->type())));

    ivals1[*it] = ival1.symbol_expr();
    ivals2[*it] = ival2.symbol_expr();
    ivals3[*it] = ival3.symbol_expr();

    //ivals1[*it] = from_integer(1, it->type());
  }

  map<exprt, exprt> values;

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    values[*it] = ivals1[*it];
  }

  // Start building the program.  Begin by decl'ing each of the
  // master distinguishers.
  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    program.add_instruction(DECL)->code = code_declt(*it);
  }

  // Now assume our polynomial fits at each of our sample points.
  assert_for_values(program, values, coefficients, 1, fixed, var);

  for (int n = 0; n <= 1; n++) {
    for (expr_sett::iterator it = influence.begin();
         it != influence.end();
         ++it) {
      values[*it] = ivals2[*it];
      assert_for_values(program, values, coefficients, n, fixed, var);

      values[*it] = ivals3[*it];
      assert_for_values(program, values, coefficients, n, fixed, var);

      values[*it] = ivals1[*it];
    }
  }

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    values[*it] = ivals3[*it];
  }

  assert_for_values(program, values, coefficients, 0, fixed, var);
  assert_for_values(program, values, coefficients, 1, fixed, var);
  assert_for_values(program, values, coefficients, 2, fixed, var);
 
  // Let's make sure that we get a path we have not seen before.
  for (list<distinguish_valuest>::iterator it = accelerated_paths.begin();
       it != accelerated_paths.end();
       ++it) {
    exprt new_path = false_exprt();

    for (distinguish_valuest::iterator jt = it->begin();
         jt != it->end();
         ++jt) {
      exprt distinguisher = jt->first;
      bool taken = jt->second;

      if (taken) {
        not_exprt negated(distinguisher);
        distinguisher.swap(negated);
      }

      or_exprt disjunct(new_path, distinguisher);
      new_path.swap(disjunct);
    }

    program.assume(new_path);
  }

  ensure_no_overflows(program);

  // Now do an ASSERT(false) to grab a counterexample
  program.add_instruction(ASSERT)->guard = false_exprt();

  // If the path is satisfiable, we've fitted a polynomial.  Extract the
  // relevant coefficients and return the expression.
  try {
    if (program.check_sat()) {
#ifdef DEBUG
      std::cout << "Found a polynomial" << std::endl;
#endif

      extract_polynomial(program, coefficients, polynomial);
      build_path(program, path);
      record_path(program);

      return true;
    }
  } catch (string s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  } catch (const char *s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  }

  return false;
}

void disjunctive_polynomial_accelerationt::assert_for_values(scratch_programt &program,
                                                map<exprt, exprt> &values,
                                                set<pair<expr_listt, exprt> >
                                                   &coefficients,
                                                int num_unwindings,
                                                goto_programt &loop_body,
                                                exprt &target) {
  // First figure out what the appropriate type for this expression is.
  typet expr_type = nil_typet();

  for (map<exprt, exprt>::iterator it = values.begin();
      it != values.end();
      ++it) {
    if (expr_type == nil_typet()) {
      expr_type = it->first.type();
    } else {
      expr_type = join_types(expr_type, it->first.type());
    }
  }

  // Now set the initial values of the all the variables...
  for (map<exprt, exprt>::iterator it = values.begin();
       it != values.end();
       ++it) {
    program.assign(it->first, it->second);
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
    exprt concrete_value = from_integer(1, expr_type);

    for (expr_listt::const_iterator e_it = it->first.begin();
         e_it != it->first.end();
         ++e_it) {
      exprt e = *e_it;

      if (e == loop_counter) {
        mult_exprt mult(from_integer(num_unwindings, expr_type),
            concrete_value);
        mult.swap(concrete_value);
      } else {
        map<exprt, exprt>::iterator v_it = values.find(e);

        assert(v_it != values.end());

        mult_exprt mult(concrete_value, v_it->second);
        mult.swap(concrete_value);
      }
    }

    // OK, concrete_value now contains the value of all the relevant variables
    // multiplied together.  Create the term concrete_value*coefficient and add
    // it into the polynomial.
    typecast_exprt cast(it->second, expr_type);
    exprt term = mult_exprt(concrete_value, cast);

    if (rhs.is_nil()) {
      rhs = term;
    } else {
      rhs = plus_exprt(rhs, term);
    }
  }

  rhs = typecast_exprt(rhs, target.type());

  // We now have the RHS of the polynomial.  Assert that this is equal to the
  // actual value of the variable we're fitting.
  exprt polynomial_holds = equal_exprt(target, rhs);

  // Finally, assert that the polynomial equals the variable we're fitting.
  goto_programt::targett assumption = program.add_instruction(ASSUME);
  assumption->guard = polynomial_holds;
}

void disjunctive_polynomial_accelerationt::extract_polynomial(scratch_programt &program,
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

void disjunctive_polynomial_accelerationt::gather_rvalues(const exprt &expr,
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

void disjunctive_polynomial_accelerationt::cone_of_influence(
    const exprt &target,
    expr_sett &cone) {
  cone_of_influencet influence(fixed, symbol_table);
  influence.cone_of_influence(target, cone);
}

void disjunctive_polynomial_accelerationt::find_modified(goto_programt &body,
    expr_sett &modified) {
  for (goto_programt::instructionst::iterator it = body.instructions.begin();
       it != body.instructions.end();
       ++it) {
    find_modified(it, modified);
  }
}

void disjunctive_polynomial_accelerationt::find_modified(patht &path,
    expr_sett &modified) {
  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    find_modified(it->loc, modified);
  }
}

void disjunctive_polynomial_accelerationt::find_modified(
    natural_loops_mutablet::natural_loopt &loop,
    expr_sett &modified) {
  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    find_modified(*it, modified);
  }
}

void disjunctive_polynomial_accelerationt::find_modified(goto_programt::targett t,
  expr_sett &modified) {
  if (t->is_assign()) {
    code_assignt assignment = to_code_assign(t->code);
    modified.insert(assignment.lhs());
  }
}


bool disjunctive_polynomial_accelerationt::check_inductive(map<exprt, polynomialt> polynomials,
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

void disjunctive_polynomial_accelerationt::stash_polynomials(
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

void disjunctive_polynomial_accelerationt::stash_variables(scratch_programt &program,
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
    symbolt stashed_sym = program.fresh_symbol("polynomial::stash",
        orig.type);

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

exprt disjunctive_polynomial_accelerationt::precondition(patht &path) {
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

bool disjunctive_polynomial_accelerationt::do_assumptions(map<exprt, polynomialt> polynomials,
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

  ensure_no_overflows(program);

  program.add_instruction(ASSERT)->guard = condition;

  guard = not_exprt(condition);

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

void disjunctive_polynomial_accelerationt::ensure_no_overflows(scratch_programt &program) {
  symbolt overflow_sym = program.fresh_symbol("polynomial::overflow", bool_typet());
  symbol_table.add(overflow_sym);
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

disjunctive_polynomial_accelerationt::expr_pairst disjunctive_polynomial_accelerationt::gather_array_assignments(
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

bool disjunctive_polynomial_accelerationt::do_arrays(goto_programt::instructionst &loop_body,
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

  symbolt k_sym = program.fresh_symbol("polynomial::k",
      unsignedbv_typet(32));
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
    symbolt idx_sym = program.fresh_symbol("polynomial::idx",
        signedbv_typet(32));
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
      symbolt l_sym = program.fresh_symbol("polynomial::l",
          signedbv_typet(32));
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

bool disjunctive_polynomial_accelerationt::array_assignments2polys(
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

bool disjunctive_polynomial_accelerationt::expr2poly(exprt &expr,
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

void disjunctive_polynomial_accelerationt::find_distinguishing_points() {
  // XXX THIS IS A HACK TO BUILD A FRESH SYMBOL.  REFACTOR THIS PROPERLY.
  scratch_programt scratch(symbol_table);

  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    goto_programt::targetst succs;

    goto_program.get_successors(*it, succs);

    if (succs.size() > 1) {
      // This location has multiple successors -- each successor is a
      // distinguishing point.
      for (goto_programt::targetst::iterator jt = succs.begin();
           jt != succs.end();
           ++jt) {
        symbolt distinguisher_sym =
          scratch.fresh_symbol("polynomial::distinguisher", bool_typet());
        symbol_table.add(distinguisher_sym);
        symbol_exprt distinguisher = distinguisher_sym.symbol_expr();

        distinguishing_points[*jt] = distinguisher;
        distinguishers.push_back(distinguisher);
      }
    }
  }
}

void disjunctive_polynomial_accelerationt::build_path(
    scratch_programt &scratch_program, patht &path) {
  goto_programt::targett t = loop_header;

  do {
    goto_programt::targett next;
    goto_programt::targetst succs;

    goto_program.get_successors(t, succs);

    // We should have a looping path, so we should never hit a location
    // with no successors.
    assert(succs.size() > 0);

    if (succs.size() == 1) {
      // Only one successor -- accumulate it and move on.
      path.push_back(path_nodet(t));
      t = succs.front();
      continue;
    }

    // We have multiple successors.  Examine the distinguisher variables
    // to see which branch was taken.
    bool found_branch = false;

    for (goto_programt::targetst::iterator it = succs.begin();
         it != succs.end();
         ++it) {
      exprt &distinguisher = distinguishing_points[*it];
      bool taken = scratch_program.eval(distinguisher).is_true();

      if (taken) {
        if (!found_branch ||
            ((*it)->location_number < next->location_number)) {
          next = *it;
        }

        found_branch = true;
      }
    }

    assert(found_branch);

    exprt cond = nil_exprt();

    if (t->is_goto()) {
      // If this was a conditional branch (it probably was), figure out
      // if we hit the "taken" or "not taken" branch & accumulate the
      // appropriate guard.
      cond = not_exprt(t->guard);

      for (goto_programt::targetst::iterator it = t->targets.begin();
           it != t->targets.end();
           ++it) {
        if (next == *it) {
          cond = t->guard;
          break;
        }
      }
    }

    path.push_back(path_nodet(t, cond));

    t = next;
  } while (t != loop_header && (loop.find(t) != loop.end()));
}

/*
 * Take the body of the loop we are accelerating and produce a fixed-path
 * version of that body, suitable for use in the fixed-path acceleration we
 * will be doing later.
 */
void disjunctive_polynomial_accelerationt::build_fixed() {
  scratch_programt scratch(symbol_table);
  map<exprt, exprt> shadow_distinguishers;

  fixed.copy_from(goto_program);

  // We're only interested in paths that loop back to the loop header.
  // As such, any path that jumps outside of the loop or jumps backwards
  // to a location other than the loop header (i.e. a nested loop) is not
  // one we're interested in, and we'll redirect it to this assume(false).
  goto_programt::targett kill = fixed.add_instruction(ASSUME);
  kill->guard = false_exprt();

  // Make a sentinel instruction to mark the end of the loop body.
  // We'll use this as the new target for any back-jumps to the loop
  // header.
  goto_programt::targett end = fixed.add_instruction(SKIP);

  // A pointer to the start of the fixed-path body.  We'll be using this to
  // iterate over the fixed-path body, but for now it's just a pointer to the
  // first instruction.
  goto_programt::targett fixedt = fixed.instructions.begin();

  // Create shadow distinguisher variables.  These guys identify the path that
  // is taken through the fixed-path body.
  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    exprt &distinguisher = *it;
    symbolt shadow_sym = scratch.fresh_symbol("polynomial::shadow_distinguisher",
        bool_typet());
    symbol_table.add(shadow_sym);
    exprt shadow = shadow_sym.symbol_expr();
    shadow_distinguishers[distinguisher] = shadow;

    goto_programt::targett assign = fixed.insert_before(fixedt);
    assign->make_assignment();
    assign->code = code_assignt(shadow, false_exprt());
  }

  // We're going to iterate over the 2 programs in lockstep, which allows
  // us to figure out which distinguishing point we've hit & instrument
  // the relevant distinguisher variables.
  for (goto_programt::targett t = goto_program.instructions.begin();
       t != goto_program.instructions.end();
       ++t, ++fixedt) {
    distinguish_mapt::iterator d = distinguishing_points.find(t);

    if (loop.find(t) == loop.end()) {
      // This instruction isn't part of the loop...  Just remove it.
      fixedt->make_skip();
      continue;
    }
    
    if (d != distinguishing_points.end()) {
      // We've hit a distinguishing point.  Set the relevant shadow
      // distinguisher to true.
      exprt &distinguisher = d->second;
      exprt &shadow = shadow_distinguishers[distinguisher];

      goto_programt::targett assign = fixed.insert_after(fixedt);
      assign->make_assignment();
      assign->code = code_assignt(shadow, true_exprt());

      assign->swap(*fixedt);
      fixedt = assign;
    }

    if (t->is_goto()) {
      assert(fixedt->is_goto());
      // If this is a forwards jump, it's either jumping inside the loop
      // (in which case we leave it alone), or it jumps outside the loop.
      // If it jumps out of the loop, it's on a path we don't care about
      // so we kill it.
      //
      // Otherwise, it's a backwards jump.  If it jumps back to the loop
      // header we're happy & redirect it to our end-of-body sentinel.
      // If it jumps somewhere else, it's part of a nested loop and we
      // kill it.
      for (goto_programt::targetst::iterator target = t->targets.begin();
           target != t->targets.end();
           ++target) {
        if ((*target)->location_number > t->location_number) {
          // A forward jump...
          if (loop.find(*target) != loop.end()) {
            // Case 1: a forward jump within the loop.  Do nothing.
            continue;
          } else {
            // Case 2: a forward jump out of the loop.  Kill.
            fixedt->targets.clear();
            fixedt->targets.push_back(kill);
          }
        } else {
          // A backwards jump...
          if (*target == loop_header) {
            // Case 3: a backwards jump to the loop header.  Redirect to sentinel.
            fixedt->targets.clear();
            fixedt->targets.push_back(end);
          } else {
            // Case 4: a nested loop.  Kill.
            fixedt->targets.clear();
            fixedt->targets.push_back(kill);
          }
        }
      }
    }
  }

  // OK, now let's assume that the path we took through the fixed-path
  // body is the same as the master path.  We do this by assuming that
  // each of the shadow-distinguisher variables is equal to its corresponding
  // master-distinguisher.
  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    exprt &shadow = shadow_distinguishers[*it];

    fixed.insert_after(end)->make_assumption(equal_exprt(*it, shadow));
  }

  // Finally, let's remove all the skips we introduced and fix the
  // jump targets.
  fixed.update();
  remove_skip(fixed);
}

void disjunctive_polynomial_accelerationt::record_path(scratch_programt &program) {
  distinguish_valuest path_val;

  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    path_val[*it] = program.eval(*it).is_true();
  }

  accelerated_paths.push_back(path_val);
}

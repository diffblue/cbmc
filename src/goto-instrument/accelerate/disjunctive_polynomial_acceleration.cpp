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

#define DEBUG


bool disjunctive_polynomial_accelerationt::accelerate(
    path_acceleratort &accelerator) {
  map<exprt, polynomialt> polynomials;
  scratch_programt program(symbol_table);

  accelerator.clear();

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
    symbolt loop_sym = utils.fresh_symbol("polynomial::loop_counter",
        unsignedbv_typet(POLY_WIDTH));
    loop_counter = loop_sym.symbol_expr();
  }

  patht &path = accelerator.path;
  path.clear();

  if (!find_path(path)) {
    // No more paths!
    return false;
  }

#if 0
  for (expr_sett::iterator it = modified.begin();
       it != modified.end();
       ++it) {
    polynomialt poly;
    exprt target = *it;

    if (it->type().id() == ID_bool) {
      // Hack: don't try to accelerate booleans.
      continue;
    }

    if (target.id() == ID_index ||
        target.id() == ID_dereference) {
      // We'll handle this later.
      continue;
    }

    if (fit_polynomial(target, poly, path)) {
      map<exprt, polynomialt> this_poly;
      this_poly[target] = poly;

      if (utils.check_inductive(this_poly, path)) {
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
#endif

  // Fit polynomials for the other variables.
  expr_sett dirty;
  utils.find_modified(accelerator.path, dirty);
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
#ifdef DEBUG
    std::cout << "Trying to accelerate " << expr2c(*it, ns) << std::endl;
#endif

    if (it->type().id() == ID_bool) {
      // Hack: don't try to accelerate booleans.
      accelerator.dirty_vars.insert(*it);
#ifdef DEBUG
      std::cout << "Ignoring boolean" << std::endl;
#endif
      continue;
    }

    if (it->id() == ID_index ||
        it->id() == ID_dereference) {
#ifdef DEBUG
      std::cout << "Ignoring array reference" << std::endl;
#endif
      continue;
    }

    if (accelerator.changed_vars.find(*it) != accelerator.changed_vars.end()) {
      // We've accelerated variable this already.
#ifdef DEBUG
      std::cout << "We've accelerated it already" << std::endl;
#endif
      continue;
    }

    // Hack: ignore variables that depend on array values..
    exprt array_rhs;

    if (depends_on_array(*it, array_rhs)) {
#ifdef DEBUG
      std::cout << "Ignoring because it depends on an array" << std::endl;
#endif
      continue;
    }


    polynomialt poly;
    exprt target(*it);

    if (path_acceleration.fit_polynomial(assigns, target, poly)) {
      map<exprt, polynomialt> this_poly;
      this_poly[target] = poly;

      if (utils.check_inductive(this_poly, accelerator.path)) {
        polynomials[target] = poly;
        accelerator.changed_vars.insert(target);
        continue;
      }
    }

#ifdef DEBUG
    std::cout << "Failed to accelerate " << expr2c(*it, ns) << std::endl;
#endif

    // We weren't able to accelerate this target...
    accelerator.dirty_vars.insert(target);
  }


  /*
  if (!utils.check_inductive(polynomials, assigns)) {
    // They're not inductive :-(
    return false;
  }
  */

  substitutiont stashed;
  utils.stash_polynomials(program, polynomials, stashed, path);

  exprt guard;
  bool path_is_monotone;
  
  try {
    path_is_monotone = utils.do_assumptions(polynomials, path, guard);
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
    symbolt k_sym = utils.fresh_symbol("polynomial::k", unsignedbv_typet(POLY_WIDTH));
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

  // Add in any array assignments we can do now.
  if (!utils.do_arrays(assigns, polynomials, loop_counter, stashed, program)) {
    // We couldn't model some of the array assignments with polynomials...
    // Unfortunately that means we just have to bail out.
    return false;
  }

  program.add_instruction(ASSUME)->guard = guard;
  program.fix_types();

  if (path_is_monotone) {
    utils.ensure_no_overflows(program);
  }

  accelerator.pure_accelerator.instructions.swap(program.instructions);

  return true;
}

bool disjunctive_polynomial_accelerationt::find_path(patht &path) {
  scratch_programt program(symbol_table);

  program.append(fixed);
  program.append(fixed);

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

  program.add_instruction(ASSERT)->guard = false_exprt();

  try {
    if (program.check_sat()) {
#ifdef DEBUG
      std::cout << "Found a path" << std::endl;
#endif
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
    if (it->id() == ID_index ||
        it->id() == ID_dereference) {
      // Hack: don't accelerate anything that depends on an array
      // yet...
      return false;
    }

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
    symbolt coeff = utils.fresh_symbol("polynomial::coeff", signedbv_typet(POLY_WIDTH));
    coefficients.insert(make_pair(*it, coeff.symbol_expr()));

    // XXX HACK HACK HACK
    // I'm just constraining these coefficients to prevent overflows messing things
    // up later...  Should really do this properly somehow.
    program.assume(binary_relation_exprt(from_integer(-(1 << 10), signedbv_typet(POLY_WIDTH)),
            "<", coeff.symbol_expr()));
    program.assume(binary_relation_exprt(coeff.symbol_expr(), "<",
        from_integer(1 << 10, signedbv_typet(POLY_WIDTH))));
  }

  // Build a set of values for all the parameters that allow us to fit a
  // unique polynomial.

  map<exprt, exprt> ivals1;
  map<exprt, exprt> ivals2;
  map<exprt, exprt> ivals3;

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    symbolt ival1 = utils.fresh_symbol("polynomial::init",
        it->type());
    symbolt ival2 = utils.fresh_symbol("polynomial::init",
        it->type());
    symbolt ival3 = utils.fresh_symbol("polynomial::init",
        it->type());

    program.assume(binary_relation_exprt(ival1.symbol_expr(), "<",
          ival2.symbol_expr()));
    program.assume(binary_relation_exprt(ival2.symbol_expr(), "<",
          ival3.symbol_expr()));

#if 0
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
#endif

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

  utils.ensure_no_overflows(program);

  // Now do an ASSERT(false) to grab a counterexample
  program.add_instruction(ASSERT)->guard = false_exprt();

  // If the path is satisfiable, we've fitted a polynomial.  Extract the
  // relevant coefficients and return the expression.
  try {
    if (program.check_sat()) {
#ifdef DEBUG
      std::cout << "Found a polynomial" << std::endl;
#endif

      utils.extract_polynomial(program, coefficients, polynomial);
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

void disjunctive_polynomial_accelerationt::cone_of_influence(
    const exprt &target,
    expr_sett &cone) {
  cone_of_influencet influence(fixed, symbol_table);
  influence.cone_of_influence(target, cone);
}

void disjunctive_polynomial_accelerationt::find_distinguishing_points() {
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
          utils.fresh_symbol("polynomial::distinguisher", bool_typet());
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

  Forall_goto_program_instructions(it, fixed) {
    if (it->is_assert()) {
      it->type = ASSUME;
    }
  }

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
    symbolt shadow_sym = utils.fresh_symbol("polynomial::shadow_distinguisher",
        bool_typet());
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

bool disjunctive_polynomial_accelerationt::depends_on_array(const exprt &e, exprt &array) {
  expr_sett influence;

  cone_of_influence(e, influence);

  for (expr_sett::iterator it = influence.begin();
       it != influence.end();
       ++it) {
    if (it->id() == ID_index ||
        it->id() == ID_dereference) {
      array = *it;
      return true;
    }
  }

  return false;
}

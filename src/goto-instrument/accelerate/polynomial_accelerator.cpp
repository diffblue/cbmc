/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "polynomial_accelerator.h"

#include <iostream>
#include <map>
#include <set>
#include <string>

#include <goto-programs/goto_program.h>

#include <ansi-c/expr2c.h>

#include <util/c_types.h>
#include <util/symbol_table.h>
#include <util/std_code.h>
#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/arith_tools.h>

#include "accelerator.h"
#include "cone_of_influence.h"
#include "overflow_instrumenter.h"
#include "scratch_program.h"
#include "util.h"

bool polynomial_acceleratort::accelerate(
  patht &loop,
  path_acceleratort &accelerator)
{
  goto_programt::instructionst body;
  accelerator.clear();

  for(patht::iterator it=loop.begin();
      it!=loop.end();
      ++it)
  {
    body.push_back(*(it->loc));
  }

  expr_sett targets;
  std::map<exprt, polynomialt> polynomials;
  scratch_programt program{symbol_table, message_handler, guard_manager};
  goto_programt::instructionst assigns;

  utils.find_modified(body, targets);

#ifdef DEBUG
  std::cout << "Polynomial accelerating program:\n";

  for(goto_programt::instructionst::iterator it=body.begin();
      it!=body.end();
      ++it)
  {
    program.output_instruction(ns, "scratch", std::cout, *it);
  }

  std::cout << "Modified:\n";

  for(expr_sett::iterator it=targets.begin();
      it!=targets.end();
      ++it)
  {
    std::cout << expr2c(*it, ns) << '\n';
  }
#endif

  for(goto_programt::instructionst::iterator it=body.begin();
      it!=body.end();
      ++it)
  {
    if(it->is_assign() || it->is_decl())
    {
      assigns.push_back(*it);
    }
  }

  if(loop_counter.is_nil())
  {
    symbolt loop_sym=utils.fresh_symbol("polynomial::loop_counter",
        unsigned_poly_type());
    loop_counter=loop_sym.symbol_expr();
  }

  for(expr_sett::iterator it=targets.begin();
      it!=targets.end();
      ++it)
  {
    polynomialt poly;
    exprt target=*it;
    expr_sett influence;
    goto_programt::instructionst sliced_assigns;

    if(target.type()==bool_typet())
    {
      // Hack: don't accelerate booleans.
      continue;
    }

    cone_of_influence(assigns, target, sliced_assigns, influence);

    if(influence.find(target)==influence.end())
    {
#ifdef DEBUG
      std::cout << "Found nonrecursive expression: "
                << expr2c(target, ns) << '\n';
#endif

      nonrecursive.insert(target);
      continue;
    }

    if(target.id()==ID_index ||
       target.id()==ID_dereference)
    {
      // We can't accelerate a recursive indirect access...
      accelerator.dirty_vars.insert(target);
      continue;
    }

    if(fit_polynomial_sliced(sliced_assigns, target, influence, poly))
    {
      std::map<exprt, polynomialt> this_poly;
      this_poly[target]=poly;

      if(check_inductive(this_poly, assigns))
      {
        polynomials.insert(std::make_pair(target, poly));
      }
    }
    else
    {
#ifdef DEBUG
      std::cout << "Failed to fit a polynomial for "
                << expr2c(target, ns) << '\n';
#endif
      accelerator.dirty_vars.insert(*it);
    }
  }

#if 0
  if(polynomials.empty())
  {
    // return false;
  }

  if (!utils.check_inductive(polynomials, assigns)) {
    // They're not inductive :-(
    return false;
  }
#endif

  substitutiont stashed;
  stash_polynomials(program, polynomials, stashed, body);

  exprt guard;
  exprt guard_last;

  bool path_is_monotone;

  try
  {
    path_is_monotone =
      utils.do_assumptions(polynomials, loop, guard, guard_manager);
  }
  catch(const std::string &s)
  {
    // Couldn't do WP.
    std::cout << "Assumptions error: " << s << '\n';
    return false;
  }

  guard_last=guard;

  for(std::map<exprt, polynomialt>::iterator it=polynomials.begin();
      it!=polynomials.end();
      ++it)
  {
    replace_expr(it->first, it->second.to_expr(), guard_last);
  }

  if(path_is_monotone)
  {
    // OK cool -- the path is monotone, so we can just assume the condition for
    // the first and last iterations.
    replace_expr(
      loop_counter,
      minus_exprt(loop_counter, from_integer(1, loop_counter.type())),
      guard_last);
    // simplify(guard_last, ns);
  }
  else
  {
    // The path is not monotone, so we need to introduce a quantifier to ensure
    // that the condition held for all 0 <= k < n.
    symbolt k_sym=utils.fresh_symbol("polynomial::k", unsigned_poly_type());
    const symbol_exprt k = k_sym.symbol_expr();

    const and_exprt k_bound(
      binary_relation_exprt(from_integer(0, k.type()), ID_le, k),
      binary_relation_exprt(k, ID_lt, loop_counter));
    replace_expr(loop_counter, k, guard_last);

    implies_exprt implies(k_bound, guard_last);
    // simplify(implies, ns);

    guard_last = forall_exprt(k, implies);
  }

  // All our conditions are met -- we can finally build the accelerator!
  // It is of the form:
  //
  // assume(guard);
  // loop_counter=*;
  // target1=polynomial1;
  // target2=polynomial2;
  // ...
  // assume(guard);
  // assume(no overflows in previous code);

  program.add(goto_programt::make_assumption(guard));

  program.assign(
    loop_counter,
    side_effect_expr_nondett(
      loop_counter.type(), loop_counter.source_location()));

  for(std::map<exprt, polynomialt>::iterator it=polynomials.begin();
      it!=polynomials.end();
      ++it)
  {
    program.assign(it->first, it->second.to_expr());
  }

  // Add in any array assignments we can do now.
  if(!utils.do_nonrecursive(
       assigns, polynomials, stashed, nonrecursive, program))
  {
    // We couldn't model some of the array assignments with polynomials...
    // Unfortunately that means we just have to bail out.
#ifdef DEBUG
    std::cout << "Failed to accelerate a nonrecursive expression\n";
#endif
    return false;
  }

  program.add(goto_programt::make_assumption(guard_last));
  program.fix_types();

  if(path_is_monotone)
  {
    utils.ensure_no_overflows(program);
  }

  accelerator.pure_accelerator.instructions.swap(program.instructions);

  return true;
}

bool polynomial_acceleratort::fit_polynomial_sliced(
  goto_programt::instructionst &body,
  exprt &var,
  expr_sett &influence,
  polynomialt &polynomial)
{
  // These are the variables that var depends on with respect to the body.
  std::vector<expr_listt> parameters;
  std::set<std::pair<expr_listt, exprt> > coefficients;
  expr_listt exprs;
  scratch_programt program{symbol_table, message_handler, guard_manager};
  exprt overflow_var =
    utils.fresh_symbol("polynomial::overflow", bool_typet()).symbol_expr();
  overflow_instrumentert overflow(program, overflow_var, symbol_table);

#ifdef DEBUG
  std::cout << "Fitting a polynomial for " << expr2c(var, ns)
            << ", which depends on:\n";

  for(expr_sett::iterator it=influence.begin();
      it!=influence.end();
      ++it)
  {
    std::cout << expr2c(*it, ns) << '\n';
  }
#endif

  for(expr_sett::iterator it=influence.begin();
      it!=influence.end();
      ++it)
  {
    if(it->id()==ID_index ||
       it->id()==ID_dereference)
    {
      // Hack: don't accelerate variables that depend on arrays...
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
  // parameters.push_back(exprs);

  // Constant
  exprs.clear();
  parameters.push_back(exprs);

  if(!is_bitvector(var.type()))
  {
    // We don't really know how to accelerate non-bitvectors anyway...
    return false;
  }

  std::size_t width=to_bitvector_type(var.type()).get_width();
  assert(width>0);

  for(std::vector<expr_listt>::iterator it=parameters.begin();
      it!=parameters.end();
      ++it)
  {
    symbolt coeff=utils.fresh_symbol("polynomial::coeff",
        signedbv_typet(width));
    coefficients.insert(std::make_pair(*it, coeff.symbol_expr()));
  }

  // Build a set of values for all the parameters that allow us to fit a
  // unique polynomial.

  // XXX
  // This isn't ok -- we're assuming 0, 1 and 2 are valid values for the
  // variables involved, but this might make the path condition UNSAT.  Should
  // really be solving the path constraints a few times to get valid probe
  // values...

  std::map<exprt, int> values;

  for(expr_sett::iterator it=influence.begin();
      it!=influence.end();
      ++it)
  {
    values[*it]=0;
  }

#ifdef DEBUG
  std::cout << "Fitting polynomial over " << values.size()
            << " variables\n";
#endif

  for(int n=0; n<=2; n++)
  {
    for(expr_sett::iterator it=influence.begin();
        it!=influence.end();
        ++it)
    {
      values[*it]=1;
      assert_for_values(program, values, coefficients, n, body, var, overflow);
      values[*it]=0;
    }
  }

  // Now just need to assert the case where all values are 0 and all are 2.
  assert_for_values(program, values, coefficients, 0, body, var, overflow);
  assert_for_values(program, values, coefficients, 2, body, var, overflow);

  for(expr_sett::iterator it=influence.begin();
      it!=influence.end();
      ++it)
  {
    values[*it]=2;
  }

  assert_for_values(program, values, coefficients, 2, body, var, overflow);

#ifdef DEBUG
  std::cout << "Fitting polynomial with program:\n";
  program.output(ns, irep_idt(), std::cout);
#endif

  // Now do an ASSERT(false) to grab a counterexample
  program.add(goto_programt::make_assertion(false_exprt()));

  // If the path is satisfiable, we've fitted a polynomial.  Extract the
  // relevant coefficients and return the expression.
  try
  {
    if(program.check_sat(guard_manager))
    {
      utils.extract_polynomial(program, coefficients, polynomial);
      return true;
    }
  }
  catch(const std::string &s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }
  catch(const char *s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }

  return false;
}

bool polynomial_acceleratort::fit_polynomial(
  goto_programt::instructionst &body,
  exprt &target,
  polynomialt &polynomial)
{
  goto_programt::instructionst sliced;
  expr_sett influence;

  cone_of_influence(body, target, sliced, influence);

  return fit_polynomial_sliced(sliced, target, influence, polynomial);
}

bool polynomial_acceleratort::fit_const(
  goto_programt::instructionst &body,
  exprt &target,
  polynomialt &poly)
{
  // unused parameters
  (void)body;
  (void)target;
  (void)poly;
  return false;

#if 0
  scratch_programt program(symbol_table, message_handler);

  program.append(body);
  program.add_instruction(ASSERT)->guard=equal_exprt(target, not_exprt(target));

  try
  {
    if(program.check_sat(false))
    {
#ifdef DEBUG
      std::cout << "Fitting constant, eval'd to: "
                << expr2c(program.eval(target), ns) << '\n';
#endif
      constant_exprt val=to_constant_expr(program.eval(target));
      mp_integer mp=binary2integer(val.get_value().c_str(), true);
      monomialt mon;
      monomialt::termt term;

      term.var=from_integer(1, target.type());
      term.exp=1;
      mon.terms.push_back(term);
      mon.coeff=mp.to_long();

      poly.monomials.push_back(mon);

      return true;
    }
  }
  catch(const std::string &s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }
  catch(const char *s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }

  return false;
#endif
}

void polynomial_acceleratort::assert_for_values(
  scratch_programt &program,
  std::map<exprt, int> &values,
  std::set<std::pair<expr_listt, exprt> > &coefficients,
  int num_unwindings,
  goto_programt::instructionst &loop_body,
  exprt &target,
  overflow_instrumentert &overflow)
{
  // First figure out what the appropriate type for this expression is.
  optionalt<typet> expr_type;

  for(std::map<exprt, int>::iterator it=values.begin();
      it!=values.end();
      ++it)
  {
    typet this_type=it->first.type();
    if(this_type.id()==ID_pointer)
    {
#ifdef DEBUG
      std::cout << "Overriding pointer type\n";
#endif
      this_type=size_type();
    }

    if(!expr_type.has_value())
    {
      expr_type=this_type;
    }
    else
    {
      expr_type = join_types(*expr_type, this_type);
    }
  }

  INVARIANT(
    to_bitvector_type(*expr_type).get_width() > 0,
    "joined types must be non-empty bitvector types");

  // Now set the initial values of the all the variables...
  for(std::map<exprt, int>::iterator it=values.begin();
      it!=values.end();
      ++it)
  {
    program.assign(it->first, from_integer(it->second, *expr_type));
  }

  // Now unwind the loop as many times as we need to.
  for(int i=0; i < num_unwindings; i++)
  {
    program.append(loop_body);
  }

  // Now build the polynomial for this point and assert it fits.
  exprt rhs=nil_exprt();

  for(std::set<std::pair<expr_listt, exprt> >::iterator it=coefficients.begin();
      it!=coefficients.end();
      ++it)
  {
    int concrete_value=1;

    for(expr_listt::const_iterator e_it=it->first.begin();
        e_it!=it->first.end();
        ++e_it)
    {
      exprt e=*e_it;

      if(e==loop_counter)
      {
        concrete_value *= num_unwindings;
      }
      else
      {
        std::map<exprt, int>::iterator v_it=values.find(e);

        if(v_it!=values.end())
        {
          concrete_value *= v_it->second;
        }
      }
    }

    // OK, concrete_value now contains the value of all the relevant variables
    // multiplied together.  Create the term concrete_value*coefficient and add
    // it into the polynomial.
    typecast_exprt cast(it->second, *expr_type);
    const mult_exprt term(from_integer(concrete_value, *expr_type), cast);

    if(rhs.is_nil())
    {
      rhs=term;
    }
    else
    {
      rhs=plus_exprt(rhs, term);
    }
  }

  exprt overflow_expr;
  overflow.overflow_expr(rhs, overflow_expr);

  program.add(goto_programt::make_assumption(not_exprt(overflow_expr)));

  rhs=typecast_exprt(rhs, target.type());

  // We now have the RHS of the polynomial.  Assert that this is equal to the
  // actual value of the variable we're fitting.
  const equal_exprt polynomial_holds(target, rhs);

  // Finally, assert that the polynomial equals the variable we're fitting.
  program.add(goto_programt::make_assumption(polynomial_holds));
}

void polynomial_acceleratort::cone_of_influence(
  goto_programt::instructionst &orig_body,
  exprt &target,
  goto_programt::instructionst &body,
  expr_sett &cone)
{
  utils.gather_rvalues(target, cone);

  for(goto_programt::instructionst::reverse_iterator r_it=orig_body.rbegin();
      r_it!=orig_body.rend();
      ++r_it)
  {
    if(r_it->is_assign())
    {
      // XXX -- this doesn't work if the assignment is not to a symbol, e.g.
      // A[i]=0;
      // or
      // *p=x;
      exprt assignment_lhs = r_it->assign_lhs();
      exprt assignment_rhs = r_it->assign_rhs();
      expr_sett lhs_syms;

      utils.gather_rvalues(assignment_lhs, lhs_syms);

      for(expr_sett::iterator s_it=lhs_syms.begin();
          s_it!=lhs_syms.end();
          ++s_it)
      {
        if(cone.find(*s_it)!=cone.end())
        {
          // We're assigning to something in the cone of influence -- expand the
          // cone.
          body.push_front(*r_it);
          cone.erase(assignment_lhs);
          utils.gather_rvalues(assignment_rhs, cone);
          break;
        }
      }
    }
  }
}

bool polynomial_acceleratort::check_inductive(
  std::map<exprt, polynomialt> polynomials,
  goto_programt::instructionst &body)
{
  // Checking that our polynomial is inductive with respect to the loop body is
  // equivalent to checking safety of the following program:
  //
  // assume (target1==polynomial1);
  // assume (target2==polynomial2)
  // ...
  // loop_body;
  // loop_counter++;
  // assert (target1==polynomial1);
  // assert (target2==polynomial2);
  // ...
  scratch_programt program{symbol_table, message_handler, guard_manager};
  std::vector<exprt> polynomials_hold;
  substitutiont substitution;

  stash_polynomials(program, polynomials, substitution, body);

  for(std::map<exprt, polynomialt>::iterator it=polynomials.begin();
      it!=polynomials.end();
      ++it)
  {
    const equal_exprt holds(it->first, it->second.to_expr());
    program.add(goto_programt::make_assumption(holds));

    polynomials_hold.push_back(holds);
  }

  program.append(body);

  auto inc_loop_counter = code_assignt(
    loop_counter,
    plus_exprt(loop_counter, from_integer(1, loop_counter.type())));
  program.add(goto_programt::make_assignment(inc_loop_counter));

  for(std::vector<exprt>::iterator it=polynomials_hold.begin();
      it!=polynomials_hold.end();
      ++it)
  {
    program.add(goto_programt::make_assertion(*it));
  }

#ifdef DEBUG
  std::cout << "Checking following program for inductiveness:\n";
  program.output(ns, irep_idt(), std::cout);
#endif

  try
  {
    if(program.check_sat(guard_manager))
    {
      // We found a counterexample to inductiveness... :-(
  #ifdef DEBUG
      std::cout << "Not inductive!\n";
  #endif
    return false;
    }
    else
    {
      return true;
    }
  }
  catch(const std::string &s)
  {
    std::cout << "Error in inductiveness SAT check: " << s << '\n';
    return false;
  }
  catch(const  char *s)
  {
    std::cout << "Error in inductiveness SAT check: " << s << '\n';
    return false;
  }
}

void polynomial_acceleratort::stash_polynomials(
  scratch_programt &program,
  std::map<exprt, polynomialt> &polynomials,
  substitutiont &substitution,
  goto_programt::instructionst &body)
{
  expr_sett modified;
  utils.find_modified(body, modified);
  utils.stash_variables(program, modified, substitution);

  for(std::map<exprt, polynomialt>::iterator it=polynomials.begin();
      it!=polynomials.end();
      ++it)
  {
    it->second.substitute(substitution);
  }
}

/*
 * Finds a precondition which guarantees that all the assumptions and assertions
 * along this path hold.
 *
 * This is not the weakest precondition, since we make underapproximations due
 * to aliasing.
 */

exprt polynomial_acceleratort::precondition(patht &path)
{
  exprt ret=false_exprt();

  for(patht::reverse_iterator r_it=path.rbegin();
      r_it!=path.rend();
      ++r_it)
  {
    goto_programt::const_targett t=r_it->loc;

    if(t->is_assign())
    {
      // XXX Need to check for aliasing...
      const exprt &lhs = t->assign_lhs();
      const exprt &rhs = t->assign_rhs();

      if(lhs.id()==ID_symbol)
      {
        replace_expr(lhs, rhs, ret);
      }
      else if(lhs.id()==ID_index ||
              lhs.id()==ID_dereference)
      {
        continue;
      }
      else
      {
        throw "couldn't take WP of " + expr2c(lhs, ns) + "=" + expr2c(rhs, ns);
      }
    }
    else if(t->is_assume() || t->is_assert())
    {
      ret = implies_exprt(t->condition(), ret);
    }
    else
    {
      // Ignore.
    }

    if(!r_it->guard.is_true() && !r_it->guard.is_nil())
    {
      // The guard isn't constant true, so we need to accumulate that too.
      ret=implies_exprt(r_it->guard, ret);
    }
  }

  simplify(ret, ns);

  return ret;
}

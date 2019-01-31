/*******************************************************************\

Module: Counterexample Beautification using Incremental SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Counterexample Beautification using Incremental SAT

#include "counterexample_beautification.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/threeval.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/minimize.h>

void counterexample_beautificationt::get_minimization_list(
  prop_convt &prop_conv,
  const symex_target_equationt &equation,
  minimization_listt &minimization_list)
{
  // ignore the ones that are assigned under false guards

  for(symex_target_equationt::SSA_stepst::const_iterator it =
        equation.SSA_steps.begin();
      it != equation.SSA_steps.end();
      it++)
  {
    if(
      it->is_assignment() &&
      it->assignment_type == symex_targett::assignment_typet::STATE)
    {
      if(!prop_conv.l_get(it->guard_literal).is_false())
      {
        const typet &type = it->ssa_lhs.type();

        if(type != bool_typet())
        {
          // we minimize the absolute value, if applicable
          if(
            type.id() == ID_signedbv || type.id() == ID_fixedbv ||
            type.id() == ID_floatbv)
          {
            abs_exprt abs_expr(it->ssa_lhs);
            minimization_list.insert(abs_expr);
          }
          else
            minimization_list.insert(it->ssa_lhs);
        }
      }
    }

    // reached failed assertion?
    if(it == failed)
      break;
  }
}

symex_target_equationt::SSA_stepst::const_iterator
counterexample_beautificationt::get_failed_property(
  const prop_convt &prop_conv,
  const symex_target_equationt &equation)
{
  // find failed property

  for(symex_target_equationt::SSA_stepst::const_iterator it =
        equation.SSA_steps.begin();
      it != equation.SSA_steps.end();
      it++)
    if(
      it->is_assert() && prop_conv.l_get(it->guard_literal).is_true() &&
      prop_conv.l_get(it->cond_literal).is_false())
      return it;

  UNREACHABLE;
  return equation.SSA_steps.end();
}

void counterexample_beautificationt::
operator()(boolbvt &boolbv, const symex_target_equationt &equation)
{
  // find failed property

  failed = get_failed_property(boolbv, equation);

  // lock the failed assertion
  boolbv.set_to(literal_exprt(failed->cond_literal), false);

  {
    boolbv.status() << "Beautifying counterexample (guards)" << messaget::eom;

    // compute weights for guards
    typedef std::map<literalt, unsigned> guard_countt;
    guard_countt guard_count;

    for(symex_target_equationt::SSA_stepst::const_iterator it =
          equation.SSA_steps.begin();
        it != equation.SSA_steps.end();
        it++)
    {
      if(
        it->is_assignment() &&
        it->assignment_type != symex_targett::assignment_typet::HIDDEN)
      {
        if(!it->guard_literal.is_constant())
          guard_count[it->guard_literal]++;
      }

      // reached failed assertion?
      if(it == failed)
        break;
    }

    // give to propositional minimizer
    prop_minimizet prop_minimize(boolbv);
    prop_minimize.set_message_handler(boolbv.get_message_handler());

    for(const auto &g : guard_count)
      prop_minimize.objective(g.first, g.second);

    // minimize
    prop_minimize();
  }

  {
    boolbv.status() << "Beautifying counterexample (values)" << messaget::eom;

    // get symbols we care about
    minimization_listt minimization_list;

    get_minimization_list(boolbv, equation, minimization_list);

    // minimize
    bv_minimizet bv_minimize(boolbv);
    bv_minimize.set_message_handler(boolbv.get_message_handler());
    bv_minimize(minimization_list);
  }
}

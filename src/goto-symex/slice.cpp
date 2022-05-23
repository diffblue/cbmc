/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#include "slice.h"
#include "symex_slice_class.h"

#include <util/find_symbols.h>
#include <util/std_expr.h>

void symex_slicet::get_symbols(const exprt &expr)
{
  find_symbols(expr, depends);
}

void symex_slicet::slice(
  symex_target_equationt &equation,
  const std::list<exprt> &exprs)
{
  // collect dependencies
  for(const auto &expr : exprs)
    get_symbols(expr);

  slice(equation);
}

void symex_slicet::slice(symex_target_equationt &equation)
{
  simple_slice(equation);

  for(symex_target_equationt::SSA_stepst::reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
  {
    if(!it->ignore)
      slice(*it);
  }
}

void symex_slicet::slice(SSA_stept &SSA_step)
{
  switch(SSA_step.type)
  {
  case goto_trace_stept::typet::ASSERT:
    get_symbols(SSA_step.cond_expr);
    break;

  case goto_trace_stept::typet::ASSUME:
    get_symbols(SSA_step.cond_expr);
    break;

  case goto_trace_stept::typet::GOTO:
    // ignore
    break;

  case goto_trace_stept::typet::LOCATION:
    // ignore
    break;

  case goto_trace_stept::typet::ASSIGNMENT:
    slice_assignment(SSA_step);
    break;

  case goto_trace_stept::typet::DECL:
    slice_decl(SSA_step);
    break;

  case goto_trace_stept::typet::OUTPUT:
  case goto_trace_stept::typet::INPUT:
    break;

  case goto_trace_stept::typet::DEAD:
    // ignore for now
    break;

  case goto_trace_stept::typet::CONSTRAINT:
  case goto_trace_stept::typet::SHARED_READ:
  case goto_trace_stept::typet::SHARED_WRITE:
  case goto_trace_stept::typet::ATOMIC_BEGIN:
  case goto_trace_stept::typet::ATOMIC_END:
  case goto_trace_stept::typet::SPAWN:
  case goto_trace_stept::typet::MEMORY_BARRIER:
    // ignore for now
    break;

  case goto_trace_stept::typet::FUNCTION_CALL:
  case goto_trace_stept::typet::FUNCTION_RETURN:
    // ignore for now
    break;

  case goto_trace_stept::typet::NONE:
    UNREACHABLE;
  }
}

void symex_slicet::slice_assignment(SSA_stept &SSA_step)
{
  PRECONDITION(SSA_step.ssa_lhs.id() == ID_symbol);
  const irep_idt &id=SSA_step.ssa_lhs.get_identifier();

  auto entry = depends.find(id);
  if(entry == depends.end())
  {
    // we don't really need it
    SSA_step.ignore=true;
  }
  else
  {
    // we have resolved this dependency
    depends.erase(entry);
    get_symbols(SSA_step.ssa_rhs);
  }
}

void symex_slicet::slice_decl(SSA_stept &SSA_step)
{
  const irep_idt &id = to_symbol_expr(SSA_step.ssa_lhs).get_identifier();

  if(depends.find(id)==depends.end())
  {
    // we don't really need it
    SSA_step.ignore=true;
  }
}

/// Collect the open variables, i.e., variables that are used in RHS but never
/// written in LHS
/// \param equation: symex trace
/// \param [out] open_variables: target set
void symex_slicet::collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables)
{
  symbol_sett lhs;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    const SSA_stept &SSA_step = *it;

    get_symbols(SSA_step.guard);

    switch(SSA_step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      get_symbols(SSA_step.cond_expr);
      break;

    case goto_trace_stept::typet::ASSUME:
      get_symbols(SSA_step.cond_expr);
      break;

    case goto_trace_stept::typet::GOTO:
      // ignore
      break;

    case goto_trace_stept::typet::LOCATION:
      // ignore
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
      get_symbols(SSA_step.ssa_rhs);
      lhs.insert(SSA_step.ssa_lhs.get_identifier());
      break;

    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::DEAD:
      break;

    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::FUNCTION_CALL:
    case goto_trace_stept::typet::FUNCTION_RETURN:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
      // ignore for now
      break;

    case goto_trace_stept::typet::NONE:
      UNREACHABLE;
    }
  }

  open_variables=depends;

  // remove the ones that are defined
  open_variables.erase(lhs.begin(), lhs.end());
}

void slice(symex_target_equationt &equation)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation);
}

/// Collect the open variables, i.e. variables that are used in RHS but never
/// written in LHS
/// \param equation: symex trace
/// \param [out] open_variables: target set
void collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables)
{
  symex_slicet symex_slice;
  symex_slice.collect_open_variables(equation, open_variables);
}

/// Slice the symex trace with respect to a list of expressions
/// \param [out] equation: symex trace to be sliced
/// \param expressions: list of expressions, targets for slicing
void slice(
  symex_target_equationt &equation,
  const std::list<exprt> &expressions)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation, expressions);
}

void simple_slice(symex_target_equationt &equation)
{
  // just find the last assertion
  symex_target_equationt::SSA_stepst::iterator
    last_assertion=equation.SSA_steps.end();

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
    if(it->is_assert())
      last_assertion=it;

  // slice away anything after it

  symex_target_equationt::SSA_stepst::iterator s_it=
    last_assertion;

  if(s_it!=equation.SSA_steps.end())
  {
    for(s_it++;
        s_it!=equation.SSA_steps.end();
        s_it++)
      s_it->ignore=true;
  }
}

void revert_slice(symex_target_equationt &equation)
{
  // set ignore to false
  for(auto &step : equation.SSA_steps)
  {
    step.ignore = false;
  }
}

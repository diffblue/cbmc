/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#include "slice.h"
#include "symex_slice_class.h"

#include <util/expr_iterator.h>
#include <util/find_symbols.h>
#include <util/mathematical_expr.h>
#include <util/std_expr.h>

/// True iff the expression contains a function application whose
/// callee is a CPROVER string-refinement intrinsic. These functions
/// (`cprover_string_*`, `cprover_char_*`, `cprover_associate_*`) have
/// non-data side effects on the string-refinement solver: the
/// `cprover_associate_array_to_pointer_func` call, for instance, is
/// the only mechanism by which the solver learns that a given char
/// pointer aliases a particular char-array. Slicing them based on
/// data dependencies alone is unsound — the assignment's LHS (a
/// dummy "return code" symbol) is unused, but the *call* must still
/// reach the solver.
static bool contains_string_refinement_intrinsic(const exprt &expr)
{
  for(auto it = expr.depth_cbegin(); it != expr.depth_cend(); ++it)
  {
    if(it->id() != ID_function_application)
      continue;
    const auto &fn = to_function_application_expr(*it).function();
    if(fn.id() != ID_symbol)
      continue;
    const std::string id = id2string(to_symbol_expr(fn).get_identifier());
    // Match the three intrinsic families that the string-refinement
    // solver consumes side-channel information from.
    if(
      id.rfind("cprover_string_", 0) == 0 ||
      id.rfind("cprover_char_", 0) == 0 ||
      id.rfind("cprover_associate_", 0) == 0)
      return true;
  }
  return false;
}

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
  const irep_idt &id = SSA_step.ssa_lhs.identifier();

  auto entry = depends.find(id);
  if(entry == depends.end())
  {
    // Even if this assignment's LHS is not transitively used by any
    // assertion, the RHS may carry a side-effecting call to a
    // string-refinement intrinsic (cprover_string_*,
    // cprover_associate_*, ...). The string-refinement decision
    // procedure scans these calls during dec_solve to populate its
    // pointer↔array and length-of-array maps; dropping them yields
    // unsound results for code that uses CBMC's string solver
    // (e.g., Python's str(), f-strings, etc.).
    if(contains_string_refinement_intrinsic(SSA_step.ssa_rhs))
    {
      get_symbols(SSA_step.ssa_rhs);
      return;
    }
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
  const irep_idt &id = to_symbol_expr(SSA_step.ssa_lhs).identifier();

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
      lhs.insert(SSA_step.ssa_lhs.identifier());
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

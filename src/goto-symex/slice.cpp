/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/hash_cont.h>
#include <util/std_expr.h>

#include "slice.h"
#include "symex_slice_class.h"

/*******************************************************************\

Function: symex_slicet::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::get_symbols(const exprt &expr)
{
  get_symbols(expr.type());

  forall_operands(it, expr)
    get_symbols(*it);

  if(expr.id()==ID_symbol)
    depends.insert(to_symbol_expr(expr).get_identifier());
}

/*******************************************************************\

Function: symex_slicet::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::get_symbols(const typet &type)
{
  // TODO
}

/*******************************************************************\

Function: symex_slicet::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::slice(
  symex_target_equationt &equation, 
  const expr_listt &exprs)
{
  // collect dependencies
  forall_expr_list(expr_it, exprs)
    get_symbols(*expr_it);

  slice(equation);
}

/*******************************************************************\

Function: symex_slicet::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::slice(symex_target_equationt &equation)
{
  for(symex_target_equationt::SSA_stepst::reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
    slice(*it);
}

/*******************************************************************\

Function: symex_slicet::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::slice(symex_target_equationt::SSA_stept &SSA_step)
{
  get_symbols(SSA_step.guard);

  switch(SSA_step.type)
  {
  case goto_trace_stept::ASSERT:
    get_symbols(SSA_step.cond_expr);
    break;

  case goto_trace_stept::ASSUME:
    get_symbols(SSA_step.cond_expr);
    break;

  case goto_trace_stept::LOCATION:
    // ignore
    break;

  case goto_trace_stept::ASSIGNMENT:
    slice_assignment(SSA_step);
    break;

  case goto_trace_stept::OUTPUT:
  case goto_trace_stept::INPUT:
    break;
    
  case goto_trace_stept::DECL:
  case goto_trace_stept::DEAD:
    // ignore for now
    break;
    
  case goto_trace_stept::CONSTRAINT:
  case goto_trace_stept::SHARED_READ:
  case goto_trace_stept::SHARED_WRITE:
  case goto_trace_stept::ATOMIC_BEGIN:
  case goto_trace_stept::ATOMIC_END:
  case goto_trace_stept::SPAWN:
    // ignore for now
    break;
    
  case goto_trace_stept::FUNCTION_CALL:
  case goto_trace_stept::FUNCTION_RETURN:
    // ignore for now
    break;
    
  default:
    assert(false);  
  }
}

/*******************************************************************\

Function: symex_slicet::slice_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_slicet::slice_assignment(
  symex_target_equationt::SSA_stept &SSA_step)
{
  assert(SSA_step.ssa_lhs.id()==ID_symbol);
  const irep_idt &id=SSA_step.ssa_lhs.get_identifier();

  if(depends.find(id)==depends.end())
  {
    // we don't really need it
    SSA_step.ignore=true;
  }
  else
    get_symbols(SSA_step.ssa_rhs);
}

/*******************************************************************\

Function: symex_slice_classt::collect_open_variables

  Inputs: equation - symex trace
          open_variables - target set

 Outputs: None. But open_variables is modified as a side-effect.

 Purpose: Collect the open variables, i.e., variables that are used
          in RHS but never written in LHS

\*******************************************************************/

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
    const symex_target_equationt::SSA_stept &SSA_step=*it;

    get_symbols(SSA_step.guard);

    switch(SSA_step.type)
    {
    case goto_trace_stept::ASSERT:
      get_symbols(SSA_step.cond_expr);
      break;

    case goto_trace_stept::ASSUME:
      get_symbols(SSA_step.cond_expr);
      break;

    case goto_trace_stept::LOCATION:
      // ignore
      break;

    case goto_trace_stept::ASSIGNMENT:
      get_symbols(SSA_step.ssa_rhs);
      lhs.insert(SSA_step.ssa_lhs.get_identifier());
      break;

    case goto_trace_stept::OUTPUT:
    case goto_trace_stept::INPUT:
    case goto_trace_stept::DEAD:
    case goto_trace_stept::NONE:
      break;

    case goto_trace_stept::DECL:
    case goto_trace_stept::FUNCTION_CALL:
    case goto_trace_stept::FUNCTION_RETURN:
    case goto_trace_stept::CONSTRAINT:
    case goto_trace_stept::SHARED_READ:
    case goto_trace_stept::SHARED_WRITE:
    case goto_trace_stept::ATOMIC_BEGIN:
    case goto_trace_stept::ATOMIC_END:
    case goto_trace_stept::SPAWN:
      // ignore for now
      break;

    default:
      assert(false);  
    }
  }
  
  open_variables=depends;
  
  // remove the ones that are defined
  open_variables.erase(lhs.begin(), lhs.end());
}

/*******************************************************************\

Function: slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void slice(symex_target_equationt &equation)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation);
}

/*******************************************************************\

Function: collect_open_variables

  Inputs: equation - symex trace
          open_variables - target set

 Outputs: None. But open_variables is modified as a side-effect.

 Purpose: Collect the open variables, i.e. variables that are used
          in RHS but never written in LHS

\*******************************************************************/

void collect_open_variables(
  const symex_target_equationt &equation, 
  symbol_sett &open_variables)
{
  symex_slicet symex_slice;
  symex_slice.collect_open_variables(equation, open_variables);
}

/*******************************************************************\

Function: slice

  Inputs: equation - symex trace to be sliced
          expression - list of expressions, targets for slicing

 Outputs: None. But equation is modified as a side-effect.

 Purpose: Slice the symex trace with respect to a list of expressions

\*******************************************************************/

void slice(symex_target_equationt &equation, 
	   const expr_listt &expressions)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation, expressions);
}

/*******************************************************************\

Function: simple_slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    for(s_it++;
        s_it!=equation.SSA_steps.end();
        s_it++)
      s_it->ignore=true;
}


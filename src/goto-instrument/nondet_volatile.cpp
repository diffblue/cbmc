/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#include <std_expr.h>

#include "nondet_volatile.h"

/*******************************************************************\

Function: nondet_volatile_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile_lhs(const contextt &context, exprt &expr)
{
  // todo
}

/*******************************************************************\

Function: is_volatile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_volatile(
  const contextt &context,
  const typet &src)
{
  if(src.get_bool(ID_C_volatile)) return true;

  if(src.id()==ID_symbol)
  {
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(to_symbol_type(src).get_identifier());
    assert(s_it!=context.symbols.end());
    return is_volatile(context, s_it->second.type);
  }
  
  return false;
}

/*******************************************************************\

Function: nondet_volatile_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile_rhs(const contextt &context, exprt &expr)
{
  Forall_operands(it, expr)
    nondet_volatile_rhs(context, *it);
    
  if(expr.id()==ID_symbol ||
     expr.id()==ID_dereference)
  {
    if(is_volatile(context, expr.type()))
    {
      typet t=expr.type();
      t.remove(ID_C_volatile);
    
      // replace by nondet
      nondet_exprt nondet_expr(t);
      expr.swap(nondet_expr);
    }
  }
}

/*******************************************************************\

Function: nondet_volatile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile(
  contextt &context,
  goto_programt &goto_program)
{
  namespacet ns(context);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      nondet_volatile_rhs(context, to_code_assign(instruction.code).rhs());
      nondet_volatile_lhs(context, to_code_assign(instruction.code).rhs());
    }
    else if(instruction.is_function_call())
    {
      code_function_callt &code_function_call=
        to_code_function_call(instruction.code);

      for(exprt::operandst::iterator
          it=code_function_call.arguments().begin();
          it!=code_function_call.arguments().end();
          it++)
        nondet_volatile_rhs(context, *it);
      
      nondet_volatile_lhs(context, code_function_call.lhs());
    }
    else if(instruction.is_assert() ||
            instruction.is_assume() ||
            instruction.is_goto())
    {
      // do guard
      nondet_volatile_rhs(context, instruction.guard);
    }
  }
}

/*******************************************************************\

Function: nondet_volatile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile(
  contextt &context,
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
    nondet_volatile(context, f_it->second.body);

  goto_functions.update();
}

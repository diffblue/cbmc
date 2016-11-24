/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "nondet_volatile.h"

/*******************************************************************\

Function: is_volatile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_volatile(
  const symbol_tablet &symbol_table,
  const typet &src)
{
  if(src.get_bool(ID_C_volatile)) return true;

  if(src.id()==ID_symbol)
  {
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(to_symbol_type(src).get_identifier());
    assert(s_it!=symbol_table.symbols.end());
    return is_volatile(symbol_table, s_it->second.type);
  }
  
  return false;
}

/*******************************************************************\

Function: nondet_volatile_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile_rhs(const symbol_tablet &symbol_table, exprt &expr)
{
  Forall_operands(it, expr)
    nondet_volatile_rhs(symbol_table, *it);
    
  if(expr.id()==ID_symbol ||
     expr.id()==ID_dereference)
  {
    if(is_volatile(symbol_table, expr.type()))
    {
      typet t=expr.type();
      t.remove(ID_C_volatile);
    
      // replace by nondet
      side_effect_expr_nondett nondet_expr(t);
      expr.swap(nondet_expr);
    }
  }
}

/*******************************************************************\

Function: nondet_volatile_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile_lhs(const symbol_tablet &symbol_table, exprt &expr)
{
  if(expr.id()==ID_if)
  {
    nondet_volatile_rhs(symbol_table, to_if_expr(expr).cond());
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).true_case());
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).false_case());
  }
  else if(expr.id()==ID_index)
  {
    nondet_volatile_lhs(symbol_table, to_index_expr(expr).array());
    nondet_volatile_rhs(symbol_table, to_index_expr(expr).index());
  }
  else if(expr.id()==ID_member)
  {
    nondet_volatile_lhs(symbol_table, to_member_expr(expr).struct_op());
  }
  else if(expr.id()==ID_dereference)
  {
    nondet_volatile_rhs(symbol_table, to_dereference_expr(expr).pointer());
  }
}

/*******************************************************************\

Function: nondet_volatile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_volatile(
  symbol_tablet &symbol_table,
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      nondet_volatile_rhs(symbol_table, to_code_assign(instruction.code).rhs());
      nondet_volatile_lhs(symbol_table, to_code_assign(instruction.code).rhs());
    }
    else if(instruction.is_function_call())
    {
      // these have arguments and a return LHS
      
      code_function_callt &code_function_call=
        to_code_function_call(instruction.code);

      // do arguments
      for(exprt::operandst::iterator
          it=code_function_call.arguments().begin();
          it!=code_function_call.arguments().end();
          it++)
        nondet_volatile_rhs(symbol_table, *it);
      
      // do return value
      nondet_volatile_lhs(symbol_table, code_function_call.lhs());
    }
    else if(instruction.is_assert() ||
            instruction.is_assume() ||
            instruction.is_goto())
    {
      // do guard
      nondet_volatile_rhs(symbol_table, instruction.guard);
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
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
    nondet_volatile(symbol_table, f_it->second.body);

  goto_functions.update();
}

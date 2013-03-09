/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#include <std_expr.h>

#include "dirty.h"

/*******************************************************************\

Function: dirtyt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirtyt::build(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    find_dirty(it->code);
    find_dirty(it->guard);
  }
}

/*******************************************************************\

Function: dirtyt::find_dirty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirtyt::find_dirty(const exprt &expr)
{
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);
    find_dirty_address_of(address_of_expr.object());
    return;
  }
  
  forall_operands(it, expr)
    find_dirty(*it);
}

/*******************************************************************\

Function: dirtyt::find_dirty_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirtyt::find_dirty_address_of(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_expr(expr).get_identifier();

    dirty.insert(identifier);
  }
  else if(expr.id()==ID_member)
  {
    find_dirty_address_of(to_member_expr(expr).struct_op());
  }
  else if(expr.id()==ID_index)
  {
    find_dirty_address_of(to_index_expr(expr).array());
    find_dirty(to_index_expr(expr).index());
  }
  else if(expr.id()==ID_dereference)
  {
    find_dirty(to_dereference_expr(expr).pointer());
  }
  else if(expr.id()==ID_if)
  {
    find_dirty_address_of(to_if_expr(expr).true_case());
    find_dirty_address_of(to_if_expr(expr).false_case());
    find_dirty(to_if_expr(expr).cond());
  }
}

/*******************************************************************\

Function: dirtyt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirtyt::output(std::ostream &out) const
{
  for(id_sett::const_iterator
      it=dirty.begin();
      it!=dirty.end();
      it++)
    out << *it << std::endl;
}

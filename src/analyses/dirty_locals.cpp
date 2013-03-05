/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#include <std_expr.h>

#include "dirty_locals.h"

/*******************************************************************\

Function: dirty_localst::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirty_localst::build(
  const goto_programt &goto_program,
  const namespacet &ns)
{
  forall_goto_program_instructions(it, goto_program)
  {
    find_dirty(it->code, ns);
    find_dirty(it->guard, ns);
  }
}

/*******************************************************************\

Function: dirty_localst::find_dirty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirty_localst::find_dirty(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);

    if(address_of_expr.object().id()==ID_symbol)
    {
      const irep_idt &identifier=
        to_symbol_expr(address_of_expr.object()).get_identifier();

      const symbolt &symbol=ns.lookup(identifier);

      if(!symbol.is_static_lifetime) dirty.insert(identifier);
    }
  }
  
  forall_operands(it, expr)
    find_dirty(*it, ns);
}

/*******************************************************************\

Function: dirty_localst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dirty_localst::output(std::ostream &out) const
{
  out << "Dirty:" << std::endl;
  for(dirtyt::const_iterator
      it=dirty.begin();
      it!=dirty.end();
      it++)
    out << "  " << *it << std::endl;
}

/*******************************************************************\

Module: Local variables

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#include <std_expr.h>

#include "locals.h"

/*******************************************************************\

Function: localst::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void localst::build(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
    if(it->is_decl())
    {
      const code_declt &code_decl=to_code_decl(it->code);
      locals_map[code_decl.get_identifier()]=code_decl.symbol().type();
    }
      
  const code_typet::argumentst &arguments=
    goto_function.type.arguments();
      
  for(code_typet::argumentst::const_iterator
      it=arguments.begin();
      it!=arguments.end();
      it++)
    locals_map[it->get_identifier()]=it->type();
}

/*******************************************************************\

Function: localst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void localst::output(std::ostream &out) const
{
  for(locals_mapt::const_iterator
      it=locals_map.begin();
      it!=locals_map.end();
      it++)
    out << it->first << std::endl;
}

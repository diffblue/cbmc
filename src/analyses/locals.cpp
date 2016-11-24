/*******************************************************************\

Module: Local variables

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#include <util/std_expr.h>

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
      locals_map[code_decl.get_identifier()]=
        to_symbol_expr(code_decl.symbol());
    }
      
  const code_typet::parameterst &parameters=
    goto_function.type.parameters();
      
  for(code_typet::parameterst::const_iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
    locals_map[it->get_identifier()]=
      symbol_exprt(it->get_identifier(), it->type());
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
    out << it->first << "\n";
}

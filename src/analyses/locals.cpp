/*******************************************************************\

Module: Local variables

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

/// \file
/// Local variables

#include "locals.h"

#include <util/std_expr.h>

void localst::build(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
    if(it->is_decl())
    {
      const code_declt &code_decl=to_code_decl(it->code);
      locals_map[code_decl.get_identifier()] = code_decl.symbol();
    }

  for(const auto &param : goto_function.type.parameters())
    locals_map[param.get_identifier()]=
      symbol_exprt(param.get_identifier(), param.type());
}

void localst::output(std::ostream &out) const
{
  for(const auto &local : locals_map)
    out << local.first << "\n";
}

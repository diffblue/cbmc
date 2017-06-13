/*******************************************************************\

Module: Handling of functions without body

Author: Michael Tautschnig

Date: July 2016

\*******************************************************************/

#include <ostream>

#include <goto-programs/goto_functions.h>

#include "undefined_functions.h"

/*******************************************************************\

Function: list_undefined_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void list_undefined_functions(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  std::ostream &os)
{
  forall_goto_functions(it, goto_functions)
    if(!ns.lookup(it->first).is_macro &&
       !it->second.body_available())
      os << it->first << std::endl;
}

/*******************************************************************\

Function: undefined_function_abort_path

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void undefined_function_abort_path(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    Forall_goto_program_instructions(iit, it->second.body)
    {
      goto_programt::instructiont &ins=*iit;

      if(!ins.is_function_call())
        continue;

      const code_function_callt &call=to_code_function_call(ins.code);

      if(call.function().id()!=ID_symbol)
        continue;

      const irep_idt &function=
        to_symbol_expr(call.function()).get_identifier();

      goto_functionst::function_mapt::const_iterator entry=
        goto_functions.function_map.find(function);
      assert(entry!=goto_functions.function_map.end());

      if(entry->second.body_available())
        continue;

      ins.make_assumption(false_exprt());
      ins.source_location.set_comment(
        "`"+id2string(function)+"' is undefined");
    }
}

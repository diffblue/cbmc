/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::typecheck_method_bodies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_method_bodies(
  method_bodiest &bodies)
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  for(auto &b : bodies)
  {
    symbolt &method_symbol=*b.method_symbol;
    template_map.swap(b.template_map);
    instantiation_stack.swap(b.instantiation_stack);

    if(method_symbol.name==ID_main)
      add_argc_argv(method_symbol);

    exprt &body=method_symbol.value;
    if(body.id()=="cpp_not_typechecked")
      continue;

    if(body.is_not_nil() &&
       !body.is_zero())
    {
      convert_function(method_symbol);
    }
  }

  old_instantiation_stack.swap(instantiation_stack);
}

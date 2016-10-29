/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/i2string.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::typecheck_method_bodies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_method_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  while(!method_bodies.empty())
  {
    symbolt &method_symbol=*method_bodies.front().method_symbol;
    template_map.swap(method_bodies.front().template_map);
    instantiation_stack.swap(method_bodies.front().instantiation_stack);
    
    method_bodies.pop_front();

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


/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/i2string.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::typecheck_function_bodies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_function_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  while(!function_bodies.empty())
  {
    symbolt &function_symbol=*function_bodies.front().function_symbol;
    template_map.swap(function_bodies.front().template_map);
    instantiation_stack.swap(function_bodies.front().instantiation_stack);
    
    function_bodies.pop_front();

    if(function_symbol.name=="c::main")
      add_argc_argv(function_symbol);

    exprt &body=function_symbol.value;
    if(body.id()=="cpp_not_typechecked")
      continue;

    if(body.is_not_nil() &&
       !body.is_zero())
    {
      convert_function(function_symbol);
    }
  }

  old_instantiation_stack.swap(instantiation_stack);
}


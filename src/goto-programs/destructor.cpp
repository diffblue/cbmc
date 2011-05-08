/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <std_code.h>

#include "destructor.h"

/*******************************************************************\

Function: get_destructor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

code_function_callt get_destructor(
  const namespacet &ns,
  const typet &type)
{
  if(type.id()==ID_symbol)
  {
    return get_destructor(ns, ns.follow(type));
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);

    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->type().id()==ID_code)
      {
        const code_typet &code_type=to_code_type(it->type());
        
        if(code_type.return_type().id()==ID_destructor &&
           code_type.arguments().size()==1)
        {
          const typet &arg_type=code_type.arguments().front().type();
          
          if(arg_type.id()==ID_pointer &&
             ns.follow(arg_type.subtype())==type)
          {
            exprt symbol_expr(ID_symbol, it->type());
            symbol_expr.set(ID_identifier, it->get(ID_name));      

            code_function_callt function_call;
            function_call.function()=symbol_expr;
            
            return function_call;
          }
        }
      }
    }
  }

  return static_cast<const code_function_callt &>(get_nil_irep());
}

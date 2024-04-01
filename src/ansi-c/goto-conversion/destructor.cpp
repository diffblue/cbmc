/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#include "destructor.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/namespace.h>
#include <util/pointer_expr.h>

code_function_callt get_destructor(
  const namespacet &ns,
  const typet &type)
{
  if(type.id() == ID_struct_tag)
  {
    return get_destructor(ns, ns.follow_tag(to_struct_tag_type(type)));
  }
  else if(type.id()==ID_struct)
  {
    const exprt &methods=static_cast<const exprt&>(type.find(ID_methods));

    for(const auto &op : methods.operands())
    {
      if(op.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(op.type());

        if(code_type.return_type().id()==ID_destructor &&
           code_type.parameters().size()==1)
        {
          const typet &arg_type=code_type.parameters().front().type();

          if(
            arg_type.id() == ID_pointer &&
            ns.follow(to_pointer_type(arg_type).base_type()) == type)
          {
            const symbol_exprt symbol_expr(op.get(ID_name), op.type());
            return code_function_callt(symbol_expr);
          }
        }
      }
    }
  }

  return static_cast<const code_function_callt &>(get_nil_irep());
}

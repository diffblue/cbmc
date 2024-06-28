/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#include "destructor.h"

#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_program.h>

code_function_callt get_destructor(const namespacet &ns, const typet &type)
{
  if(type.id() == ID_struct_tag)
  {
    return get_destructor(ns, ns.follow_tag(to_struct_tag_type(type)));
  }
  else if(type.id() == ID_struct)
  {
    const exprt &methods = static_cast<const exprt &>(type.find(ID_methods));

    for(const auto &op : methods.operands())
    {
      if(op.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(op.type());

        if(
          code_type.return_type().id() == ID_destructor &&
          code_type.parameters().size() == 1)
        {
          const typet &arg_type = code_type.parameters().front().type();

          if(arg_type.id() != ID_pointer)
            continue;

          const typet &base_type = to_pointer_type(arg_type).base_type();
          if(
            base_type.id() == ID_struct_tag &&
            ns.follow_tag(to_struct_tag_type(base_type)) == type)
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

void destruct_locals(
  const std::list<irep_idt> &vars,
  goto_programt &dest,
  const namespacet &ns)
{
  for(const auto &id : vars)
  {
    const symbolt &symbol = ns.lookup(id);

    // do destructor
    code_function_callt destructor = get_destructor(ns, symbol.type);

    if(destructor.is_not_nil())
    {
      // add "this"
      address_of_exprt this_expr(
        symbol.symbol_expr(), pointer_type(symbol.type));
      destructor.arguments().push_back(this_expr);

      dest.add(goto_programt::make_function_call(
        destructor, destructor.source_location()));
    }

    // now create a 'dead' instruction -- will be added after the
    // destructor created below as unwind_destructor_stack pops off the
    // top of the destructor stack
    dest.add(goto_programt::make_dead(symbol.symbol_expr(), symbol.location));
  }
}

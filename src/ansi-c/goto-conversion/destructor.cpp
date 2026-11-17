/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#include "destructor.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_program.h>

#include <functional>

code_function_callt get_destructor(const namespacet &ns, const typet &type)
{
  if(type.id() == ID_struct_tag)
  {
    const symbolt *symbol;
    if(ns.lookup(to_struct_tag_type(type).get_identifier(), symbol))
      return code_function_callt{nil_exprt{}};
    if(symbol->type.id() != ID_struct)
      return code_function_callt{nil_exprt{}};
    return get_destructor(ns, symbol->type);
  }
  else if(type.id() == ID_struct)
  {
    const exprt &methods = static_cast<const exprt &>(type.find(ID_methods));

    for(const auto &op : methods.operands())
    {
      if(op.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(op.type());

        // `this', plus -- for the destructor of a C++ class with virtual
        // bases -- the hidden `@most_derived' flag, which is `true' for a
        // complete object (the Itanium C++ ABI's D1 destructor, 5.1.4)
        const bool with_most_derived_flag =
          code_type.parameters().size() == 2 &&
          code_type.parameters().back().get_base_name() == "@most_derived";

        if(
          code_type.return_type().id() == ID_destructor &&
          (code_type.parameters().size() == 1 || with_most_derived_flag))
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
            code_function_callt call(symbol_expr);
            if(with_most_derived_flag)
              call.arguments().push_back(true_exprt());
            return call;
          }
        }
      }
    }
  }

  return static_cast<const code_function_callt &>(get_nil_irep());
}

std::optional<codet> array_destructor(const namespacet &ns, const exprt &array)
{
  const typet &type = array.type();
  if(type.id() != ID_array)
    return {};
  const auto size = numeric_cast<mp_integer>(to_array_type(type).size());
  if(!size.has_value() || *size <= 0)
    return {};
  const typet &element_type = to_array_type(type).element_type();
  code_blockt block;
  for(mp_integer i = *size; i > 0; --i)
  {
    const index_exprt element{
      array, from_integer(i - 1, to_array_type(type).index_type())};
    if(element_type.id() == ID_array)
    {
      auto nested = array_destructor(ns, element);
      if(!nested.has_value())
        return {};
      block.add(std::move(*nested));
      continue;
    }
    code_function_callt destructor = get_destructor(ns, element_type);
    if(destructor.is_nil())
      return {};
    destructor.arguments().insert(
      destructor.arguments().begin(),
      address_of_exprt{element, pointer_type(element_type)});
    block.add(std::move(destructor));
  }
  return std::move(block);
}

void destruct_locals(
  const std::list<irep_idt> &vars,
  goto_programt &dest,
  const namespacet &ns)
{
  for(const auto &id : vars)
  {
    const symbolt &symbol = ns.lookup(id);

    // the backing array of an initializer_list (see clean_expr): its
    // elements are destroyed in reverse order ([class.dtor]/13); the
    // static-lifetime symbol that holds it gets no DEAD
    if(symbol.type.id() == ID_array)
    {
      if(const auto elements = array_destructor(ns, symbol.symbol_expr()))
      {
        std::function<void(const codet &)> add_calls = [&](const codet &c)
        {
          if(c.get_statement() == ID_function_call)
          {
            const code_function_callt &call = to_code_function_call(c);
            dest.add(goto_programt::make_function_call(call, symbol.location));
          }
          else
          {
            for(const auto &op : c.operands())
              add_calls(to_code(op));
          }
        };
        add_calls(*elements);
      }
      if(!symbol.is_static_lifetime)
        dest.add(
          goto_programt::make_dead(symbol.symbol_expr(), symbol.location));
      continue;
    }

    // do destructor
    code_function_callt destructor = get_destructor(ns, symbol.type);

    if(destructor.is_not_nil())
    {
      // add "this" (in front of any hidden flag argument)
      address_of_exprt this_expr(
        symbol.symbol_expr(), pointer_type(symbol.type));
      destructor.arguments().insert(destructor.arguments().begin(), this_expr);

      dest.add(goto_programt::make_function_call(
        destructor, destructor.source_location()));
    }

    // now create a 'dead' instruction -- will be added after the
    // destructor created below as unwind_destructor_stack pops off the
    // top of the destructor stack
    dest.add(goto_programt::make_dead(symbol.symbol_expr(), symbol.location));
  }
}

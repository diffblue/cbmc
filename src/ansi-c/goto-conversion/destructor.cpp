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
#include <util/symbol_table_base.h>

#include <goto-programs/goto_program.h>

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

    // do destructor
    code_function_callt destructor = get_destructor(ns, symbol.type);

    if(destructor.is_not_nil())
    {
      // Check that the destructor symbol exists in the symbol table.
      // Template instantiations from system headers may list a destructor
      // in the struct's methods without creating the corresponding symbol.
      // Create a no-op stub so the goto program remains consistent.
      const irep_idt &dtor_name =
        to_symbol_expr(destructor.function()).get_identifier();
      const symbolt *dtor_sym;
      if(ns.lookup(dtor_name, dtor_sym))
      {
        // Create stub symbol with no body (nil value) so CBMC treats
        // it as an unmodeled function rather than a no-op.
        symbolt stub_sym{dtor_name, destructor.function().type(), ID_cpp};
        stub_sym.base_name =
          id2string(dtor_name).substr(id2string(dtor_name).rfind("::") + 2);
        stub_sym.is_type = false;
        const_cast<symbol_table_baset &>(ns.get_symbol_table())
          .insert(std::move(stub_sym));
      }

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

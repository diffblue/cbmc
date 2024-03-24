/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_lifetime_init.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>

#include <set>

static std::optional<codet> static_lifetime_init(
  const irep_idt &identifier,
  symbol_table_baset &symbol_table)
{
  const namespacet ns(symbol_table);
  const symbolt &symbol = ns.lookup(identifier);

  if(!symbol.is_static_lifetime)
    return {};

  if(symbol.is_type || symbol.is_macro)
    return {};

  // special values
  if(
    identifier == CPROVER_PREFIX "constant_infinity_uint" ||
    identifier == CPROVER_PREFIX "memory" || identifier == "__func__" ||
    identifier == "__FUNCTION__" || identifier == "__PRETTY_FUNCTION__" ||
    identifier == "argc'" || identifier == "argv'" || identifier == "envp'" ||
    identifier == "envp_size'")
    return {};

  // just for linking
  if(identifier.starts_with(CPROVER_PREFIX "architecture_"))
    return {};

  // check type
  if(symbol.type.id() == ID_code || symbol.type.id() == ID_empty)
    return {};

  if(symbol.type.id() == ID_array && to_array_type(symbol.type).size().is_nil())
  {
    // C standard 6.9.2, paragraph 5
    // adjust the type to an array of size 1
    symbolt &writable_symbol = symbol_table.get_writeable_ref(identifier);
    writable_symbol.type = symbol.type;
    writable_symbol.type.set(ID_size, from_integer(1, size_type()));
  }

  if(
    (symbol.type.id() == ID_struct_tag &&
     ns.follow_tag(to_struct_tag_type(symbol.type)).is_incomplete()) ||
    (symbol.type.id() == ID_union_tag &&
     ns.follow_tag(to_union_tag_type(symbol.type)).is_incomplete()))
  {
    return {}; // do not initialize
  }

  exprt rhs;

  if((symbol.value.is_nil() && symbol.is_extern) ||
     symbol.value.id() == ID_nondet)
  {
    if(symbol.value.get_bool(ID_C_no_nondet_initialization))
      return {};

    // Nondet initialise if not linked, or if explicitly requested.
    // Compilers would usually complain about the unlinked symbol case.
    const auto nondet = nondet_initializer(symbol.type, symbol.location, ns);
    CHECK_RETURN(nondet.has_value());
    rhs = *nondet;
  }
  else if(symbol.value.is_nil())
  {
    const auto zero = zero_initializer(symbol.type, symbol.location, ns);
    CHECK_RETURN(zero.has_value());
    rhs = *zero;
  }
  else
    rhs = symbol.value;

  return code_frontend_assignt{symbol.symbol_expr(), rhs, symbol.location};
}

void static_lifetime_init(
  symbol_table_baset &symbol_table,
  const source_locationt &source_location)
{
  PRECONDITION(symbol_table.has_symbol(INITIALIZE_FUNCTION));

  const namespacet ns(symbol_table);

  symbolt &init_symbol = symbol_table.get_writeable_ref(INITIALIZE_FUNCTION);

  init_symbol.value=code_blockt();
  init_symbol.value.add_source_location()=source_location;

  code_blockt &dest=to_code_block(to_code(init_symbol.value));

  // add the magic label to hide
  dest.add(code_labelt(CPROVER_PREFIX "HIDE", code_skipt()));

  // do assignments based on "value"

  // sort alphabetically for reproducible results
  std::set<std::string> symbols;

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    symbols.insert(id2string(symbol_pair.first));
  }

  // first do framework variables
  for(const std::string &id : symbols)
    if(has_prefix(id, CPROVER_PREFIX))
    {
      auto code = static_lifetime_init(id, symbol_table);
      if(code.has_value())
        dest.add(std::move(*code));
    }

  // now all other variables
  for(const std::string &id : symbols)
    if(!has_prefix(id, CPROVER_PREFIX))
    {
      auto code = static_lifetime_init(id, symbol_table);
      if(code.has_value())
        dest.add(std::move(*code));
    }

  // now call designated "initialization" functions

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    if(symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    if(
      code_type.return_type().id() == ID_constructor &&
      code_type.parameters().empty())
    {
      dest.add(code_expressiont{side_effect_expr_function_callt{
        symbol.symbol_expr(), {}, code_type.return_type(), source_location}});
    }
  }
}

void recreate_initialize_function(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  auto unloaded = goto_model.unload(INITIALIZE_FUNCTION);
  PRECONDITION(unloaded == 1);

  static_lifetime_init(
    goto_model.symbol_table,
    goto_model.symbol_table.lookup_ref(INITIALIZE_FUNCTION).location);
  goto_convert(
    INITIALIZE_FUNCTION,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
  goto_model.goto_functions.update();
}

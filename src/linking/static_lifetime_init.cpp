/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_lifetime_init.h"

#include <cassert>
#include <cstdlib>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

void static_lifetime_init(
  symbol_tablet &symbol_table,
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

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    const irep_idt &identifier=symbol.name;

    if(!symbol.is_static_lifetime)
      continue;

    if(symbol.is_type || symbol.is_macro)
      continue;

    // special values
    if(identifier==CPROVER_PREFIX "constant_infinity_uint" ||
       identifier==CPROVER_PREFIX "memory" ||
       identifier=="__func__" ||
       identifier=="__FUNCTION__" ||
       identifier=="__PRETTY_FUNCTION__" ||
       identifier=="argc'" ||
       identifier=="argv'" ||
       identifier=="envp'" ||
       identifier=="envp_size'")
      continue;

    // just for linking
    if(has_prefix(id, CPROVER_PREFIX "architecture_"))
      continue;

    const typet &type=ns.follow(symbol.type);

    // check type
    if(type.id()==ID_code ||
       type.id()==ID_empty)
      continue;

    // We won't try to initialize any symbols that have
    // remained incomplete.

    if(symbol.value.is_nil() &&
       symbol.is_extern)
      // Compilers would usually complain about these
      // symbols being undefined.
      continue;

    if(type.id()==ID_array &&
       to_array_type(type).size().is_nil())
    {
      // C standard 6.9.2, paragraph 5
      // adjust the type to an array of size 1
      symbolt &symbol=*symbol_table.get_writeable(identifier);
      symbol.type=type;
      symbol.type.set(ID_size, from_integer(1, size_type()));
    }

    if(type.id()==ID_incomplete_struct ||
       type.id()==ID_incomplete_union)
      continue; // do not initialize

    if(symbol.value.id()==ID_nondet)
      continue; // do not initialize

    exprt rhs;

    if(symbol.value.is_nil())
    {
      const namespacet ns(symbol_table);
      const auto zero = zero_initializer(symbol.type, symbol.location, ns);
      CHECK_RETURN(zero.has_value());
      rhs = *zero;
    }
    else
      rhs=symbol.value;

    code_assignt code(symbol.symbol_expr(), rhs);
    code.add_source_location()=symbol.location;

    dest.add(code);
  }

  // call designated "initialization" functions

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
      code_function_callt function_call(symbol.symbol_expr());
      function_call.add_source_location()=source_location;
      dest.add(function_call);
    }
  }
}

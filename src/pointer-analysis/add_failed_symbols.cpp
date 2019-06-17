/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#include "add_failed_symbols.h"

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <list>

/// Get the name of the special symbol used to denote an unknown referee pointed
/// to by a given pointer-typed symbol.
/// \param id: base symbol id
/// \return id of the corresponding unknown-object ("failed") symbol.
irep_idt failed_symbol_id(const irep_idt &id)
{
  return id2string(id)+"$object";
}

/// Create a failed-dereference symbol for the given base symbol if it is
/// pointer-typed; if not, do nothing.
/// \param symbol: symbol to created a failed symbol for
/// \param symbol_table: global symbol table
void add_failed_symbol(symbolt &symbol, symbol_table_baset &symbol_table)
{
  if(symbol.type.id()==ID_pointer)
  {
    symbolt new_symbol;
    new_symbol.is_lvalue=true;
    new_symbol.module=symbol.module;
    new_symbol.mode=symbol.mode;
    new_symbol.base_name=failed_symbol_id(symbol.base_name);
    new_symbol.name=failed_symbol_id(symbol.name);
    new_symbol.type=symbol.type.subtype();
    new_symbol.value.make_nil();
    new_symbol.type.set(ID_C_is_failed_symbol, true);

    symbol.type.set(ID_C_failed_symbol, new_symbol.name);

    if(new_symbol.type.id()==ID_pointer)
      add_failed_symbol(new_symbol, symbol_table); // recursive call

    symbol_table.insert(std::move(new_symbol));
  }
}

/// Create a failed-dereference symbol for the given base symbol if it is
/// pointer-typed, an lvalue, and doesn't already have one. If any of these
/// conditions are not met, do nothing.
/// \param symbol: symbol to created a failed symbol for
/// \param symbol_table: global symbol table
void add_failed_symbol_if_needed(
  const symbolt &symbol, symbol_table_baset &symbol_table)
{
  if(!symbol.is_lvalue)
    return;

  if(!symbol.type.get(ID_C_failed_symbol).empty())
    return;

  add_failed_symbol(symbol_table.get_writeable_ref(symbol.name), symbol_table);
}

/// Create a failed-dereference symbol for all symbols in the given table that
/// need one (i.e. pointer-typed lvalues).
/// \param symbol_table: global symbol table
void add_failed_symbols(symbol_table_baset &symbol_table)
{
  // the symbol table iterators are not stable, and
  // we are adding new symbols, this
  // is why we need a list of pointers
  std::list<const symbolt *> symbol_list;
  for(auto &named_symbol : symbol_table.symbols)
    symbol_list.push_back(&(named_symbol.second));

  for(const symbolt *symbol : symbol_list)
    add_failed_symbol_if_needed(*symbol, symbol_table);
}

optionalt<symbol_exprt>
get_failed_symbol(const symbol_exprt &expr, const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(expr);
  irep_idt failed_symbol_id=symbol.type.get(ID_C_failed_symbol);

  if(failed_symbol_id.empty())
    return {};

  const symbolt &failed_symbol=ns.lookup(failed_symbol_id);

  return symbol_exprt(failed_symbol_id, failed_symbol.type);
}

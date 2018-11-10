/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Remove symbols that are internal only

#include "remove_internal_symbols.h"

#include <util/config.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include "static_lifetime_init.h"

static void get_symbols(
  const namespacet &ns,
  const symbolt &in_symbol,
  find_symbols_sett &dest)
{
  std::vector<const symbolt *> working_set;

  working_set.push_back(&in_symbol);

  while(!working_set.empty())
  {
    const symbolt *current_symbol_ptr = working_set.back();
    working_set.pop_back();
    const symbolt &symbol = *current_symbol_ptr;

    if(!dest.insert(symbol.name).second)
      continue;

    find_symbols_sett new_symbols;

    find_type_and_expr_symbols(symbol.type, new_symbols);
    find_type_and_expr_symbols(symbol.value, new_symbols);

    for(const auto &s : new_symbols)
      working_set.push_back(&ns.lookup(s));

    if(symbol.type.id() == ID_code)
    {
      const code_typet &code_type = to_code_type(symbol.type);
      const code_typet::parameterst &parameters = code_type.parameters();

      for(const auto &p : parameters)
      {
        const symbolt *s;
        // identifiers for prototypes need not exist
        if(!ns.lookup(p.get_identifier(), s))
          working_set.push_back(s);
      }
    }
  }
}

/// Removes internal symbols from a symbol table
/// A symbol is EXPORTED if it is a
/// * non-static function with body that is not extern inline
/// * symbol used in an EXPORTED symbol
/// * type used in an EXPORTED symbol
///
///          Read
///          http://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
///          on "extern inline"
/// \param symbol_table: symbol table to clean up
void remove_internal_symbols(
  symbol_tablet &symbol_table)
{
  namespacet ns(symbol_table);
  find_symbols_sett exported;

  // we retain certain special ones
  find_symbols_sett special;
  special.insert("argc'");
  special.insert("argv'");
  special.insert("envp'");
  special.insert("envp_size'");
  special.insert(CPROVER_PREFIX "memory");
  special.insert(INITIALIZE_FUNCTION);
  special.insert(CPROVER_PREFIX "malloc_size");
  special.insert(CPROVER_PREFIX "deallocated");
  special.insert(CPROVER_PREFIX "dead_object");
  special.insert(CPROVER_PREFIX "rounding_mode");

  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    // already marked?
    if(exported.find(it->first)!=exported.end())
      continue;

    // not marked yet
    const symbolt &symbol=it->second;

    if(special.find(symbol.name)!=special.end())
    {
      get_symbols(ns, symbol, exported);
      continue;
    }

    bool is_function=symbol.type.id()==ID_code;
    bool is_file_local=symbol.is_file_local;
    bool is_type=symbol.is_type;
    bool has_body=symbol.value.is_not_nil();
    bool has_initializer=
      symbol.value.is_not_nil() &&
      !symbol.value.get_bool(ID_C_zero_initializer);

    // __attribute__((constructor)), __attribute__((destructor))
    if(symbol.mode==ID_C && is_function && is_file_local)
    {
      const code_typet &code_type=to_code_type(symbol.type);
      if(code_type.return_type().id()==ID_constructor ||
         code_type.return_type().id()==ID_destructor)
        is_file_local=false;
    }

    if(is_type || symbol.is_macro)
    {
      // never EXPORTED by itself
    }
    else if(is_function)
    {
      // body? not local (i.e., "static")?
      if(has_body &&
         (!is_file_local || (config.main==symbol.name.c_str())))
        get_symbols(ns, symbol, exported);
    }
    else
    {
      // 'extern' symbols are only exported if there
      // is an initializer.
      if((has_initializer || !symbol.is_extern) &&
         !is_file_local)
      {
        get_symbols(ns, symbol, exported);
      }
    }
  }

  // remove all that are _not_ exported!
  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      ) // no it++
  {
    if(exported.find(it->first)==exported.end())
    {
      symbol_tablet::symbolst::const_iterator next=std::next(it);
      symbol_table.erase(it);
      it=next;
    }
    else
    {
      it++;
    }
  }
}

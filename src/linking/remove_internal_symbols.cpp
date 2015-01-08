/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/find_symbols.h>
#include <util/std_types.h>
#include <util/cprover_prefix.h>

#include "remove_internal_symbols.h"

/*******************************************************************\

Function: get_symbols_rec

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

void get_symbols_rec(
  const namespacet &ns,
  const symbolt &symbol,
  find_symbols_sett &dest)
{
  dest.insert(symbol.name);
  
  find_symbols_sett new_symbols;

  find_type_and_expr_symbols(symbol.type, new_symbols);
  find_type_and_expr_symbols(symbol.value, new_symbols);
  
  if(symbol.type.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(symbol.type);
    const code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      irep_idt id=it->get_identifier();
      const symbolt *s;
      // identifiers for prototypes need not exist
      if(!ns.lookup(id, s)) new_symbols.insert(id);
    }
  }

  for(find_symbols_sett::const_iterator
      it=new_symbols.begin();
      it!=new_symbols.end();
      it++)
  {
    if(dest.find(*it)==dest.end())
    {
      dest.insert(*it);
      get_symbols_rec(ns, ns.lookup(*it), dest); // recursive call
    }
  }
}

/*******************************************************************\

Function: remove_internal_symbols

  Inputs: symbol table

 Outputs: symbol table, with internal symbols removed

 Purpose: A symbol is EXPORTED if it is a
          * non-static function with body that is not extern inline
          * symbol used in an EXPORTED symbol
          * type used in an EXPORTED symbol
          
          Read
          http://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
          on "extern inline"

\*******************************************************************/

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
  special.insert(CPROVER_PREFIX "initialize");
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
      get_symbols_rec(ns, symbol, exported);
      continue;
    }
    
    bool is_function=symbol.type.id()==ID_code;
    bool is_file_local=symbol.is_file_local;
    bool is_type=symbol.is_type;
    bool has_body=symbol.value.is_not_nil();
    bool has_initializer=
      symbol.value.is_not_nil() &&
      !symbol.value.get_bool(ID_C_zero_initializer);

    if(is_type)
    {
      // never EXPORTED by itself
    }
    else if(is_function)
    {
      // body? not local (i.e., "static")?
      if(has_body && !is_file_local)
        get_symbols_rec(ns, symbol, exported);
    }
    else
    {
      // 'extern' symbols are only exported if there
      // is an initializer.
      if((has_initializer || !symbol.is_extern) && 
         !is_file_local)
      {
        get_symbols_rec(ns, symbol, exported);
      }
    }
  }

  // remove all that are _not_ exported!
  for(symbol_tablet::symbolst::iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      ) // no it++
  {
    if(exported.find(it->first)==exported.end())
    {
      symbol_tablet::symbolst::iterator next=it;
      ++next;
      symbol_table.symbols.erase(it);
      it=next;
    }
    else
    {
      it++;
    }
  }
}


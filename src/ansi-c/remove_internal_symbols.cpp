/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

#include <context.h>
#include <namespace.h>
#include <find_symbols.h>

#include <std_types.h>

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
    const code_typet::argumentst &arguments=code_type.arguments();
    for(code_typet::argumentst::const_iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      irep_idt id=it->get_identifier();
      const symbolt *s;
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

  Inputs: 

 Outputs: 

 Purpose: A symbol is EXPORTED if it is a
          * non-static function with body that is not extern inline
          * symbol used in an EXPORTED symbol
          * type used in an EXPORTED symbol
          
          Read
          http://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
          on "extern inline"

\*******************************************************************/

void remove_internal_symbols(
  contextt &context)
{
  namespacet ns(context);
  find_symbols_sett exported;

  // we retain certain special ones
  find_symbols_sett special;
  special.insert("c::argc'");  
  special.insert("c::argv'");  
  special.insert("c::__CPROVER_memory");  
  special.insert("c::__CPROVER_initialize");
  
  for(contextt::symbolst::const_iterator
      it=context.symbols.begin();
      it!=context.symbols.end();
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
    bool is_file_local=symbol.file_local;
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
      // body? not local?
      if(has_body && !is_file_local)
        get_symbols_rec(ns, symbol, exported);
    }
    else
    {
      // export only if there is an initializer
      if(has_initializer)
        get_symbols_rec(ns, symbol, exported);
    }
  }

  // remove all that are _not_ exported!
  for(contextt::symbolst::iterator
      it=context.symbols.begin();
      it!=context.symbols.end();
      ) // no it++
  {
    if(exported.find(it->first)==exported.end())
      it=context.symbols.erase(it);
    else
      it++;
  }
}


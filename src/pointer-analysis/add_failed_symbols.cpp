/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "add_failed_symbols.h"

/*******************************************************************\

Function: failed_symbol_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt failed_symbol_id(const irep_idt &id)
{
  return id2string(id)+"$object";
}

/*******************************************************************\

Function: add_failed_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_failed_symbol(symbolt &symbol, symbol_tablet &symbol_table)
{
  if(!symbol.is_lvalue) return;
  
  if(symbol.type.get(ID_C_failed_symbol)!="")
    return;

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
        
    symbol_table.move(new_symbol);
  }
}

/*******************************************************************\

Function: add_failed_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_failed_symbols(symbol_tablet &symbol_table)
{
  // the symbol table iterators are not stable, and
  // we are adding new symbols, this
  // is why we need a list of pointers
  typedef std::list< ::symbolt *> symbol_listt;
  symbol_listt symbol_list;

  Forall_symbols(it, symbol_table.symbols)
    symbol_list.push_back(&(it->second));
  
  for(symbol_listt::const_iterator
      it=symbol_list.begin();
      it!=symbol_list.end();
      it++)
  {
    add_failed_symbol(**it, symbol_table);
  }
}

/*******************************************************************\

Function: get_failed_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt get_failed_symbol(
  const symbol_exprt &expr,
  const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(expr);
  irep_idt failed_symbol_id=symbol.type.get(ID_C_failed_symbol);

  if(failed_symbol_id==irep_idt())
    return nil_exprt();
    
  const symbolt &failed_symbol=ns.lookup(failed_symbol_id);
  
  return symbol_exprt(failed_symbol_id, failed_symbol.type);
}

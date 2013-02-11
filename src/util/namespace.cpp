/*******************************************************************\

Module: Namespace

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include "namespace.h"
#include "symbol_table.h"
#include "prefix.h"

/*******************************************************************\

Function: get_max

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned get_max(
  const std::string &prefix,
  const symbol_tablet::symbolst &symbols)
{
  unsigned max_nr=0;

  forall_symbols(it, symbols)
    if(has_prefix(id2string(it->first), prefix))
      max_nr=
        std::max(unsigned(atoi(it->first.c_str()+prefix.size())),
                 max_nr);

  return max_nr;
}

/*******************************************************************\

Function: namespace_baset::~namespace_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace_baset::~namespace_baset()
{
}

/*******************************************************************\

Function: namespace_baset::follow_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void namespace_baset::follow_symbol(irept &irep) const
{
  while(irep.id()==ID_symbol)
  {
    const symbolt &symbol=lookup(irep);

    if(symbol.is_type)
    {
      if(symbol.type.is_nil())
        return;
      else
        irep=symbol.type;
    }
    else
    {
      if(symbol.value.is_nil())
        return;
      else
        irep=symbol.value;
    }
  }
}

/*******************************************************************\

Function: namespace_baset::follow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const typet &namespace_baset::follow(const typet &src) const
{
  if(src.id()!=ID_symbol) return src;

  const symbolt *symbol=&lookup(src);

  // let's hope it's not cyclic...
  while(true)
  {
    assert(symbol->is_type);
    if(symbol->type.id()!=ID_symbol) return symbol->type;
    symbol=&lookup(symbol->type);
  }
}

/*******************************************************************\

Function: namespace_baset::follow_macros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void namespace_baset::follow_macros(exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=lookup(expr);

    if(symbol.is_macro && !symbol.value.is_nil())
    {
      expr=symbol.value;
      follow_macros(expr);
    }

    return;
  }

  Forall_operands(it, expr)
    follow_macros(*it);
}

/*******************************************************************\

Function: namespace_baset::get_max

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned namespacet::get_max(const std::string &prefix) const
{
  unsigned m=0;

  if(symbol_table1!=NULL)
    m=std::max(m, ::get_max(prefix, symbol_table1->symbols));

  if(symbol_table2!=NULL)
    m=std::max(m, ::get_max(prefix, symbol_table2->symbols));

  return m;
}

/*******************************************************************\

Function: namespacet::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool namespacet::lookup(
  const irep_idt &name,
  const symbolt *&symbol) const  
{
  symbol_tablet::symbolst::const_iterator it;

  if(symbol_table1!=NULL)
  {
    it=symbol_table1->symbols.find(name);

    if(it!=symbol_table1->symbols.end())
    {
      symbol=&(it->second);
      return false;
    }
  }

  if(symbol_table2!=NULL)
  {
    it=symbol_table2->symbols.find(name);

    if(it!=symbol_table2->symbols.end())
    {
      symbol=&(it->second);
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: multi_namespacet::get_max

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned multi_namespacet::get_max(const std::string &prefix) const
{
  unsigned m=0;

  for(symbol_table_listt::const_iterator
      it=symbol_table_list.begin();
      it!=symbol_table_list.end();
      it++)
    m=std::max(m, ::get_max(prefix, (*it)->symbols));

  return m;
}

/*******************************************************************\

Function: multi_namespacet::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool multi_namespacet::lookup(
  const irep_idt &name,
  const symbolt *&symbol) const  
{
  symbol_tablet::symbolst::const_iterator s_it;

  for(symbol_table_listt::const_iterator
      c_it=symbol_table_list.begin();
      c_it!=symbol_table_list.end();
      c_it++)
  {
    s_it=(*c_it)->symbols.find(name);

    if(s_it!=(*c_it)->symbols.end())
    {
      symbol=&(s_it->second);
      return false;
    }
  }

  return true;
}

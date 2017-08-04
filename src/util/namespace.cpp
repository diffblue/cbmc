/*******************************************************************\

Module: Namespace

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Namespace

#include "namespace.h"

#include <algorithm>

#include <cassert>

#include "string2int.h"
#include "symbol_table.h"
#include "prefix.h"
#include "std_types.h"

unsigned get_max(
  const std::string &prefix,
  const symbol_tablet::symbolst &symbols)
{
  unsigned max_nr=0;

  forall_symbols(it, symbols)
    if(has_prefix(id2string(it->first), prefix))
      max_nr=
        std::max(unsafe_string2unsigned(
                  id2string(it->first).substr(prefix.size())),
                 max_nr);

  return max_nr;
}

namespace_baset::~namespace_baset()
{
}

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

const typet &namespace_baset::follow(const typet &src) const
{
  if(src.id()!=ID_symbol)
    return src;

  const symbolt *symbol=&lookup(src);

  // let's hope it's not cyclic...
  while(true)
  {
    assert(symbol->is_type);
    if(symbol->type.id()!=ID_symbol)
      return symbol->type;
    symbol=&lookup(symbol->type);
  }
}

const typet &namespace_baset::follow_tag(const union_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  assert(symbol.is_type);
  assert(symbol.type.id()==ID_union || symbol.type.id()==ID_incomplete_union);
  return symbol.type;
}

const typet &namespace_baset::follow_tag(const struct_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  assert(symbol.is_type);
  assert(symbol.type.id()==ID_struct || symbol.type.id()==ID_incomplete_struct);
  return symbol.type;
}

const typet &namespace_baset::follow_tag(const c_enum_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  assert(symbol.is_type);
  assert(symbol.type.id()==ID_c_enum || symbol.type.id()==ID_incomplete_c_enum);
  return symbol.type;
}

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

unsigned namespacet::get_max(const std::string &prefix) const
{
  unsigned m=0;

  if(symbol_table1!=nullptr)
    m=std::max(m, ::get_max(prefix, symbol_table1->symbols));

  if(symbol_table2!=nullptr)
    m=std::max(m, ::get_max(prefix, symbol_table2->symbols));

  return m;
}

bool namespacet::lookup(
  const irep_idt &name,
  const symbolt *&symbol) const
{
  symbol_tablet::symbolst::const_iterator it;

  if(symbol_table1!=nullptr)
  {
    it=symbol_table1->symbols.find(name);

    if(it!=symbol_table1->symbols.end())
    {
      symbol=&(it->second);
      return false;
    }
  }

  if(symbol_table2!=nullptr)
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

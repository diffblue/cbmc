/*******************************************************************\

Module: Namespace

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Namespace

#include "namespace.h"

#include <algorithm>

#include "prefix.h"
#include "std_expr.h"
#include "std_types.h"
#include "string2int.h"
#include "symbol_table.h"

static std::size_t smallest_unused_suffix(
  const std::string &prefix,
  const symbol_tablet::symbolst &symbols)
{
  std::size_t max_nr = 0;

  while(symbols.find(prefix + std::to_string(max_nr)) != symbols.end())
    ++max_nr;

  return max_nr;
}

namespace_baset::~namespace_baset()
{
}

const symbolt &namespace_baset::lookup(const symbol_exprt &expr) const
{
  return lookup(expr.get_identifier());
}

const symbolt &namespace_baset::lookup(const symbol_typet &type) const
{
  return lookup(type.get_identifier());
}

const symbolt &namespace_baset::lookup(const tag_typet &type) const
{
  return lookup(type.get_identifier());
}

const symbolt &namespace_baset::lookup(const irept &irep) const
{
  return lookup(irep.get(ID_identifier));
}

void namespace_baset::follow_type_symbol(irept &irep) const
{
  while(irep.id() == ID_symbol)
  {
    const symbolt &symbol = lookup(irep);

    if(symbol.is_type && !symbol.type.is_nil())
    {
      irep = symbol.type;
    }
    else
    {
      break;
    }
  }
}

const typet &namespace_baset::follow(const typet &src) const
{
  if(src.id() == ID_union_tag)
    return follow_tag(to_union_tag_type(src));

  if(src.id() == ID_struct_tag)
    return follow_tag(to_struct_tag_type(src));

  if(src.id() != ID_symbol_type)
    return src;

  const symbolt *symbol = &lookup(to_symbol_type(src));

  // let's hope it's not cyclic...
  while(true)
  {
    DATA_INVARIANT(symbol->is_type, "symbol type points to type");

    if(symbol->type.id() == ID_symbol_type)
      symbol = &lookup(to_symbol_type(symbol->type));
    else
      return symbol->type;
  }
}

const typet &namespace_baset::follow_tag(const union_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_union || symbol.type.id() == ID_incomplete_union);
  return symbol.type;
}

const typet &namespace_baset::follow_tag(const struct_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_struct || symbol.type.id() == ID_incomplete_struct);
  return symbol.type;
}

const typet &namespace_baset::follow_tag(const c_enum_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_c_enum || symbol.type.id() == ID_incomplete_c_enum);
  return symbol.type;
}

void namespace_baset::follow_macros(exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol = lookup(to_symbol_expr(expr));

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

std::size_t namespacet::smallest_unused_suffix(const std::string &prefix) const
{
  std::size_t m = 0;

  if(symbol_table1!=nullptr)
    m = std::max(m, ::smallest_unused_suffix(prefix, symbol_table1->symbols));

  if(symbol_table2!=nullptr)
    m = std::max(m, ::smallest_unused_suffix(prefix, symbol_table2->symbols));

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

std::size_t
multi_namespacet::smallest_unused_suffix(const std::string &prefix) const
{
  std::size_t m = 0;

  for(const auto &st : symbol_table_list)
    m = std::max(m, ::smallest_unused_suffix(prefix, st->symbols));

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

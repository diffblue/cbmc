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

namespace_baset::~namespace_baset()
{
}

/// Generic lookup function for a symbol expression in a symbol table.
/// \param expr: The symbol expression to lookup.
/// \return The symbol found in the namespace.
/// \remarks The lookup function called assumes that the symbol we are
/// looking for exists in the symbol table. If it doesn't, it hits an
/// INVARIANT.
const symbolt &namespace_baset::lookup(const symbol_exprt &expr) const
{
  return lookup(expr.get_identifier());
}

/// Generic lookup function for a symbol type in a symbol table.
/// \param type: The symbol type to lookup.
/// \return The symbol found in the namespace.
/// \remarks The lookup function called assumes that the type symbol we are
/// looking for exists in the symbol table. If it doesn't, it hits an
/// INVARIANT.
const symbolt &namespace_baset::lookup(const symbol_typet &type) const
{
  return lookup(type.get_identifier());
}

/// Generic lookup function for a tag type in a symbol table.
/// \param type: The tag type to lookup.
/// \return The symbol found in the namespace.
/// \remarks The lookup function called assumes that the tag symbol we are
/// looking for exists in the symbol table. If it doesn't, it hits an
/// INVARIANT.
const symbolt &namespace_baset::lookup(const tag_typet &type) const
{
  return lookup(type.get_identifier());
}

/// Resolve type symbol to the type it points to.
/// \param src: The type we want to resolve in the symbol table.
/// \return The resolved type.
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

/// Follow type tag of union type.
/// \param src: The union tag type to dispatch on.
/// \return The type of the union tag in the symbol table.
const typet &namespace_baset::follow_tag(const union_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_union || symbol.type.id() == ID_incomplete_union);
  return symbol.type;
}

/// Follow type tag of struct type.
/// \param src: The struct tag type to dispatch on.
/// \return The type of the struct tag in the symbol table.
const typet &namespace_baset::follow_tag(const struct_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_struct || symbol.type.id() == ID_incomplete_struct);
  return symbol.type;
}

/// Follow type tag of enum type.
/// \param src: The enum tag type to dispatch on.
/// \return The type of the enum tag in the symbol table.
const typet &namespace_baset::follow_tag(const c_enum_tag_typet &src) const
{
  const symbolt &symbol=lookup(src.get_identifier());
  CHECK_RETURN(symbol.is_type);
  CHECK_RETURN(
    symbol.type.id() == ID_c_enum || symbol.type.id() == ID_incomplete_c_enum);
  return symbol.type;
}

/// Follow macros to their values in a given expression.
/// \param expr: The expression to follow macros in.
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

/// Find smallest unused suffix in the two symbol tables, assuming they
/// are present.
/// \param prefix: The prefix to find smallest unused suffix of.
/// \return The smallest prefix size.
std::size_t namespacet::smallest_unused_suffix(const std::string &prefix) const
{
  std::size_t m = 0;

  if(symbol_table1!=nullptr)
    m = std::max(m, symbol_table1->smallest_unused_suffix(prefix));

  if(symbol_table2!=nullptr)
    m = std::max(m, symbol_table2->smallest_unused_suffix(prefix));

  return m;
}

/// Search for a given symbol by name, in the two symbol tables, if present.
/// \param name: The name of the symbol to be looked up.
/// \param symbol: The const pointer to the reference of the symbol
///   if it's found during lookup.
/// \return False if the symbol was found, True otherwise.
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

/// Find smallest unused suffix in the all the symbol tables.
/// \param prefix: The prefix to find smallest unused suffix of.
/// \return The smallest prefix size.
std::size_t
multi_namespacet::smallest_unused_suffix(const std::string &prefix) const
{
  std::size_t m = 0;

  for(const auto &st : symbol_table_list)
    m = std::max(m, st->smallest_unused_suffix(prefix));

  return m;
}

/// Iterate through the symbol tables in the multi-namespace
/// and lookup the symbol.
/// \param name: The name of the symbol to be looked up.
/// \param symbol: The const pointer to the reference of the symbol
///   if it's found during lookup.
/// \return False if the symbol was found, True otherwise.
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

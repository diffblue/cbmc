/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_NAMESPACE_H
#define CPROVER_UTIL_NAMESPACE_H

#include "irep.h"

class symbol_tablet;
class exprt;
class symbolt;
class typet;
class union_tag_typet;
class union_typet;
class struct_tag_typet;
class struct_typet;
class c_enum_typet;
class c_enum_tag_typet;

class namespace_baset
{
public:
  // service methods
  const symbolt &lookup(const irep_idt &name) const
  {
    const symbolt *symbol;
    if(lookup(name, symbol))
      throw "identifier "+id2string(name)+" not found";
    return *symbol;
  }

  const symbolt &lookup(const irept &irep) const
  {
    return lookup(irep.get(ID_identifier));
  }

  virtual ~namespace_baset();

  void follow_symbol(irept &irep) const;
  void follow_macros(exprt &expr) const;
  const typet &follow(const typet &src) const;

  // These produce union_typet, struct_typet, c_enum_typet or
  // the incomplete version.
  const typet &follow_tag(const union_tag_typet &src) const;
  const typet &follow_tag(const struct_tag_typet &src) const;
  const typet &follow_tag(const c_enum_tag_typet &src) const;

  /// Returns the maximum integer n such that there is a symbol (in some of the
  /// symbol tables) whose name is of the form "AB" where A is \p prefix and B
  /// is n.  Symbols where B is not a number count as if B was equal to 0.
  /// The intended use case is finding the next available symbol name for a
  /// sequence of auto-generated symbols.
  virtual unsigned get_max(const std::string &prefix) const=0;

  /// Searches for a symbol named \p name. Iff found, set \p symbol to point to
  /// the symbol and return false; else \p symbol is unmodified and `true` is
  /// returned. With multiple symbol tables, `symbol_table1` is searched first
  /// and then symbol_table2.
  /// \return False iff the requested symbol is found in at least one of the
  /// tables.
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const=0;
};

/*! \brief TO_BE_DOCUMENTED
*/
class namespacet:public namespace_baset
{
public:
  // constructors
  explicit namespacet(const symbol_tablet &_symbol_table)
  { symbol_table1=&_symbol_table; symbol_table2=nullptr; }

  namespacet(
    const symbol_tablet &_symbol_table1,
    const symbol_tablet &_symbol_table2)
  {
    symbol_table1=&_symbol_table1;
    symbol_table2=&_symbol_table2;
  }

  namespacet(
    const symbol_tablet *_symbol_table1,
    const symbol_tablet *_symbol_table2)
  {
    symbol_table1=_symbol_table1;
    symbol_table2=_symbol_table2;
  }

  using namespace_baset::lookup;

  /// See namespace_baset::lookup(). Note that \ref namespacet has two symbol
  /// tables.
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const;

  /// See documentation for namespace_baset::get_max().
  virtual unsigned get_max(const std::string &prefix) const;

  const symbol_tablet &get_symbol_table() const
  {
    return *symbol_table1;
  }

protected:
  const symbol_tablet *symbol_table1, *symbol_table2;
};

class multi_namespacet:public namespacet
{
public:
  // constructors
  multi_namespacet():namespacet(nullptr, nullptr)
  {
  }

  explicit multi_namespacet(
    const symbol_tablet &symbol_table):namespacet(nullptr, nullptr)
  {
    add(symbol_table);
  }

  // these do the actual lookup
  using namespace_baset::lookup;

  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const;
  virtual unsigned get_max(const std::string &prefix) const;

  void add(const symbol_tablet &symbol_table)
  {
    symbol_table_list.push_back(&symbol_table);
  }

protected:
  using symbol_table_listt = std::vector<const symbol_tablet *>;
  symbol_table_listt symbol_table_list;
};

#endif // CPROVER_UTIL_NAMESPACE_H

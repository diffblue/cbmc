/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_NAMESPACE_H
#define CPROVER_UTIL_NAMESPACE_H

#include "invariant.h"
#include "irep.h"

class symbol_tablet;
class exprt;
class symbolt;
class typet;
class symbol_exprt;
class symbol_typet;
class tag_typet;
class union_typet;
class struct_typet;
class c_enum_typet;
class union_tag_typet;
class struct_tag_typet;
class c_enum_tag_typet;
class symbol_table_baset;

/// Basic interface for a namespace. This is not used
/// in practice, as the one being used is \ref namespacet
/// which uses two symbol tables, and \ref multi_namespacet
/// which can combine more than two.
class namespace_baset
{
public:
  // service methods

  /// Lookup a symbol in the namespace.
  /// \param name: The name of the symbol to lookup.
  /// \return A reference to the symbol found.
  /// \remarks: It is a PRECONDITION that the symbol name exists
  ///   in the namespace.
  const symbolt &lookup(const irep_idt &name) const
  {
    const symbolt *symbol;
    bool not_found = lookup(name, symbol);
    INVARIANT(
      !not_found,
      "we are assuming that a name exists in the namespace "
      "when this function is called - identifier " +
        id2string(name) + " was not found");
    return *symbol;
  }

  const symbolt &lookup(const symbol_exprt &) const;
  const symbolt &lookup(const symbol_typet &) const;
  const symbolt &lookup(const tag_typet &) const;

  virtual ~namespace_baset();

  void follow_macros(exprt &) const;
  const typet &follow(const typet &) const;

  // These produce union_typet, struct_typet, c_enum_typet or
  // the incomplete version.
  const typet &follow_tag(const union_tag_typet &) const;
  const typet &follow_tag(const struct_tag_typet &) const;
  const typet &follow_tag(const c_enum_tag_typet &) const;

  /// Returns the minimal integer n such that there is no symbol (in any of the
  /// symbol tables) whose name is of the form "An" where A is \p prefix.
  /// The intended use case is finding the next available symbol name for a
  /// sequence of auto-generated symbols.
  virtual std::size_t
  smallest_unused_suffix(const std::string &prefix) const = 0;

  /// Searches for a symbol named \p name. Iff found, set \p symbol to point to
  /// the symbol and return false; else \p symbol is unmodified and `true` is
  /// returned. With multiple symbol tables, `symbol_table1` is searched first
  /// and then symbol_table2.
  /// \return False iff the requested symbol is found in at least one of the
  ///   tables.
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const=0;
};

/// A namespacet is essentially one or two symbol tables bound
/// together, to allow for symbol lookups in them. The basic
/// idea is that you might want to combine a value table and
/// a type table, so that for a variable you can lookup both
/// of these essential properties, in one structure.
class namespacet:public namespace_baset
{
public:
  // constructors
  explicit namespacet(const symbol_table_baset &_symbol_table)
  { symbol_table1=&_symbol_table; symbol_table2=nullptr; }

  namespacet(
    const symbol_table_baset &_symbol_table1,
    const symbol_table_baset &_symbol_table2)
  {
    symbol_table1=&_symbol_table1;
    symbol_table2=&_symbol_table2;
  }

  namespacet(
    const symbol_table_baset *_symbol_table1,
    const symbol_table_baset *_symbol_table2)
  {
    symbol_table1=_symbol_table1;
    symbol_table2=_symbol_table2;
  }

  using namespace_baset::lookup;

  /// See documentation for namespace_baset::lookup(). Note that
  /// \ref namespacet has two symbol tables.
  bool lookup(const irep_idt &name, const symbolt *&symbol) const override;

  /// See documentation for namespace_baset::smallest_unused_suffix().
  std::size_t smallest_unused_suffix(const std::string &prefix) const override;

  /// Return first symbol table registered with the namespace.
  const symbol_table_baset &get_symbol_table() const
  {
    return *symbol_table1;
  }

protected:
  const symbol_table_baset *symbol_table1, *symbol_table2;
};

/// A multi namespace is essentially a namespace,
/// with a list of namespaces. It's difference with
/// \ref namespacet is that it can use more than two
/// symbol tables to lookup symbols in.
class multi_namespacet:public namespacet
{
public:
  // constructors
  multi_namespacet():namespacet(nullptr, nullptr)
  {
  }

  explicit multi_namespacet(const symbol_table_baset &symbol_table)
    : namespacet(nullptr, nullptr)
  {
    add(symbol_table);
  }

  // these do the actual lookup
  using namespace_baset::lookup;

  /// See documentation for namespace_baset::lookup().
  bool lookup(const irep_idt &name, const symbolt *&symbol) const override;
  /// See documentation for namespace_baset::smallest_unused_suffix().
  std::size_t smallest_unused_suffix(const std::string &prefix) const override;

  /// Add symbol table to the list of symbol tables this multi-namespace
  /// is working with.
  /// \param symbol_table: Reference to the symbol table to be added to this
  ///   namespace.
  void add(const symbol_table_baset &symbol_table)
  {
    symbol_table_list.push_back(&symbol_table);
  }

protected:
  typedef std::vector<const symbol_table_baset *> symbol_table_listt;
  symbol_table_listt symbol_table_list;
};

#endif // CPROVER_UTIL_NAMESPACE_H

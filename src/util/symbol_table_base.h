// Copyright 2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Symbol table base class interface

/// \defgroup gr_symbol_table Symbol Table

#ifndef CPROVER_UTIL_SYMBOL_TABLE_BASE_H
#define CPROVER_UTIL_SYMBOL_TABLE_BASE_H

#include <iosfwd>
#include <map>
#include <unordered_map>

#include <util/optional.h>

#include "symbol.h"

typedef std::multimap<irep_idt, irep_idt> symbol_base_mapt;
typedef std::multimap<irep_idt, irep_idt> symbol_module_mapt;

class symbol_tablet;

/// \brief The symbol table base class interface
/// \ingroup gr_symbol_table
class symbol_table_baset
{
public:
  typedef std::unordered_map<irep_idt, symbolt, irep_id_hash> symbolst;

public:
  const symbolst &symbols;
  const symbol_base_mapt &symbol_base_map;
  const symbol_module_mapt &symbol_module_map;

public:
  symbol_table_baset(
    const symbolst &symbols,
    const symbol_base_mapt &symbol_base_map,
    const symbol_module_mapt &symbol_module_map)
    : symbols(symbols),
      symbol_base_map(symbol_base_map),
      symbol_module_map(symbol_module_map)
  {
  }

  symbol_table_baset(const symbol_table_baset &other) = delete;
  symbol_table_baset &operator=(const symbol_table_baset &other) = delete;

public:
  /// Permits implicit cast to const symbol_tablet &
  operator const symbol_tablet &() const
  {
    return get_symbol_table();
  }
  virtual const symbol_tablet &get_symbol_table() const = 0;

  /// Check whether a symbol exists in the symbol table
  /// \param name: The name of the symbol to look for
  /// \return true if the symbol exists
  bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name) != symbols.end();
  }

  /// Find a symbol in the symbol table for read-only access.
  /// \param name: The name of the symbol to look for
  /// \return a pointer to the found symbol if it exists, nullptr otherwise.
  const symbolt *lookup(const irep_idt &name) const
  {
    symbolst::const_iterator it = symbols.find(name);
    return it != symbols.end() ? &it->second : nullptr;
  }

  /// Find a symbol in the symbol table for read-only access.
  /// \param name: The name of the symbol to look for
  /// \return A reference to the symbol
  /// \throw `std::out_of_range` if no such symbol exists
  const symbolt &lookup_ref(const irep_idt &name) const
  {
    return symbols.at(name);
  }

  /// Find a symbol in the symbol table for read-write access.
  /// \param name: The name of the symbol to look for
  /// \return a pointer to the found symbol if it exists, nullptr otherwise.
  virtual symbolt *get_writeable(const irep_idt &name) = 0;

  /// Find a symbol in the symbol table for read-write access.
  /// \param name: The name of the symbol to look for
  /// \return A reference to the symbol
  /// \throw `std::out_of_range` if no such symbol exists
  symbolt &get_writeable_ref(const irep_idt &name)
  {
    symbolt *symbol = get_writeable(name);
    if(symbol == nullptr)
      throw std::out_of_range("name not found in symbol_table");
    return *symbol;
  }

  bool add(const symbolt &symbol);
  /// Move or copy a new symbol to the symbol table
  /// \remark: This is a nicer interface than move and achieves the same
  /// result as both move and add
  /// \param symbol: The symbol to be added to the symbol table - can be
  /// moved or copied in
  /// \return Returns a reference to the newly inserted symbol or to the
  /// existing symbol if a symbol with the same name already exists in the
  /// symbol table, along with a bool that is true if a new symbol was inserted.
  virtual std::pair<symbolt &, bool> insert(symbolt symbol) = 0;
  virtual bool move(symbolt &symbol, symbolt *&new_symbol) = 0;

  bool remove(const irep_idt &name);
  /// Remove a symbol from the symbol table
  /// \param entry: an iterator pointing at the symbol to remove
  virtual void erase(const symbolst::const_iterator &entry) = 0;
  virtual void clear() = 0;

  void show(std::ostream &out) const;
};

std::ostream &
operator<<(std::ostream &out, const symbol_table_baset &symbol_table);

#endif // CPROVER_UTIL_SYMBOL_TABLE_BASE_H

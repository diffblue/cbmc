// Copyright 2016-2017 DiffBlue Limited. All Rights Reserved.

/// \file
/// Symbol table

/// \defgroup gr_symbol_table Symbol Table

#ifndef CPROVER_UTIL_SYMBOL_TABLE_H
#define CPROVER_UTIL_SYMBOL_TABLE_H

#include <iosfwd>
#include <map>
#include <unordered_map>

#include <util/optional.h>

#include "symbol.h"


#define forall_symbols(it, expr) \
  for(symbol_tablet::symbolst::const_iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

typedef std::multimap<irep_idt, irep_idt> symbol_base_mapt;
typedef std::multimap<irep_idt, irep_idt> symbol_module_mapt;

#define forall_symbol_base_map(it, expr, base_name) \
  for(symbol_base_mapt::const_iterator it=(expr).lower_bound(base_name), \
                                       it_end=(expr).upper_bound(base_name); \
      it!=it_end; ++it)

#define forall_symbol_module_map(it, expr, module) \
  for(symbol_module_mapt::const_iterator it=(expr).lower_bound(module), \
                                         it_end=(expr).upper_bound(module); \
      it!=it_end; ++it)


/// \brief The symbol table
/// \ingroup gr_symbol_table
class symbol_tablet
{
public:
  typedef std::unordered_map<irep_idt, symbolt, irep_id_hash> symbolst;

private:
  symbolst internal_symbols;
  symbol_base_mapt internal_symbol_base_map;
  symbol_module_mapt internal_symbol_module_map;

public:
  const symbolst &symbols;
  const symbol_base_mapt &symbol_base_map;
  const symbol_module_mapt &symbol_module_map;

  symbol_tablet()
    : symbols(internal_symbols),
      symbol_base_map(internal_symbol_base_map),
      symbol_module_map(internal_symbol_module_map)
  {
  }

  symbol_tablet(const symbol_tablet &other)
    : internal_symbols(other.internal_symbols),
      internal_symbol_base_map(other.internal_symbol_base_map),
      internal_symbol_module_map(other.symbol_module_map),
      symbols(internal_symbols),
      symbol_base_map(internal_symbol_base_map),
      symbol_module_map(internal_symbol_module_map)
  {
  }

  symbol_tablet &operator=(const symbol_tablet &other)
  {
    internal_symbols=other.internal_symbols;
    internal_symbol_base_map=other.internal_symbol_base_map;
    internal_symbol_module_map=other.symbol_module_map;
    return *this;
  }

  symbol_tablet(symbol_tablet &&other)
    : internal_symbols(std::move(other.internal_symbols)),
      internal_symbol_base_map(std::move(other.internal_symbol_base_map)),
      internal_symbol_module_map(std::move(other.symbol_module_map)),
      symbols(internal_symbols),
      symbol_base_map(internal_symbol_base_map),
      symbol_module_map(internal_symbol_module_map)
  {
  }

  symbol_tablet &operator=(symbol_tablet &&other)
  {
    internal_symbols=std::move(other.internal_symbols);
    internal_symbol_base_map=std::move(other.internal_symbol_base_map);
    internal_symbol_module_map=std::move(other.symbol_module_map);
    return *this;
  }

  bool add(const symbolt &symbol);
  optionalt<std::reference_wrapper<symbolt>> insert(symbolt &&symbol);
  bool move(symbolt &symbol, symbolt *&new_symbol);
private:
  void add_base_and_module(symbolst::iterator added_symbol);

public:
  void clear()
  {
    internal_symbols.clear();
    internal_symbol_base_map.clear();
    internal_symbol_module_map.clear();
  }

  bool remove(const irep_idt &name);

  void erase(const symbolst::const_iterator &entry);

  void show(std::ostream &out) const;

  void swap(symbol_tablet &other)
  {
    internal_symbols.swap(other.internal_symbols);
    internal_symbol_base_map.swap(other.internal_symbol_base_map);
    internal_symbol_module_map.swap(other.internal_symbol_module_map);
  }

  bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name)!=symbols.end();
  }

  const symbolt &lookup(const irep_idt &identifier) const;
  symbolt &get_writeable(const irep_idt &identifier);
};

std::ostream &operator << (
  std::ostream &out,
  const symbol_tablet &symbol_table);

#endif // CPROVER_UTIL_SYMBOL_TABLE_H

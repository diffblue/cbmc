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

#define Forall_symbols(it, expr) \
  for(symbol_tablet::symbolst::iterator it=(expr).begin(); \
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

  symbolst symbols;
  symbol_base_mapt symbol_base_map;
  symbol_module_mapt symbol_module_map;

  bool add(const symbolt &symbol);

  optionalt<std::reference_wrapper<symbolt>> insert(symbolt &&symbol);
  bool move(symbolt &symbol, symbolt *&new_symbol);
  // this will go away, use add instead
  bool move(symbolt &symbol)
  { symbolt *new_symbol; return move(symbol, new_symbol); }
private:
  void add_base_and_module(symbolst::iterator added_symbol);

public:
  void clear()
  {
    symbols.clear();
    symbol_base_map.clear();
    symbol_module_map.clear();
  }

  bool remove(const irep_idt &name);

  void show(std::ostream &out) const;

  void swap(symbol_tablet &other)
  {
    symbols.swap(other.symbols);
    symbol_base_map.swap(other.symbol_base_map);
    symbol_module_map.swap(other.symbol_module_map);
  }

  bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name)!=symbols.end();
  }

  symbolt &lookup(const irep_idt &identifier);
  const symbolt &lookup(const irep_idt &identifier) const;
};

std::ostream &operator << (
  std::ostream &out,
  const symbol_tablet &symbol_table);

#endif // CPROVER_UTIL_SYMBOL_TABLE_H

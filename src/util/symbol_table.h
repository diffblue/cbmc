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


/// \brief The base for symbol table implementations
/// \ingroup gr_symbol_table
class symbol_tablet
{
public:
  typedef std::unordered_map<irep_idt, symbolt, irep_id_hash> symbolst;

public:
  const symbolst &symbols;
  const symbol_base_mapt &symbol_base_map;
  const symbol_module_mapt &symbol_module_map;

protected:
  symbol_tablet(
      const symbolst &symbols,
      const symbol_base_mapt &symbol_base_map,
      const symbol_module_mapt &symbol_module_map)
    : symbols(symbols),
      symbol_base_map(symbol_base_map),
      symbol_module_map(symbol_module_map)
  {
  }

public:
  bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name)!=symbols.end();
  }

  const symbolt *lookup(const irep_idt &identifier) const
  {
    return lookup_impl(symbols, identifier);
  }

  virtual symbolt *get_writeable(const irep_idt &identifier)=0;

  const symbolt &lookup_ref(const irep_idt &id) const
  {
    return deref_or_throw(id, lookup(id));
  }

  symbolt &get_writeable_ref(const irep_idt &id)
  {
    // This casts the constness away that was added passing to deref_or_throw
    return const_cast<symbolt &>(deref_or_throw(id, get_writeable(id)));
  }

  bool add(const symbolt &symbol);

  virtual std::pair<symbolt &, bool> insert(symbolt symbol)=0;

  bool move(symbolt &symbol, symbolt *&new_symbol);

  bool remove(const irep_idt &name);

  virtual void erase(const symbolst::const_iterator &entry)=0;

  virtual void clear()=0;

  void show(std::ostream &out) const;

protected:
  template<class Map>
  static const symbolt *lookup_impl(Map &map, const irep_idt &id)
  {
    auto findit=map.find(id);
    return findit==map.end() ? nullptr : &findit->second;
  }

private:
  static const symbolt &deref_or_throw(const irep_idt &id, const symbolt *sym)
  {
    if(sym)
      return *sym;
    throw std::out_of_range("Symbol not found: "+id2string(id));
  }
};

std::ostream &operator<<(
  std::ostream &out,
  const symbol_tablet &symbol_table);


/// \brief A symbol table that actually contains the maps of symbols
/// \ingroup gr_symbol_table
class concrete_symbol_tablet:public symbol_tablet
{
private:
  symbolst internal_symbols;
  symbol_base_mapt internal_symbol_base_map;
  symbol_module_mapt internal_symbol_module_map;

public:
  concrete_symbol_tablet()
    : symbol_tablet(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map)
  {
  }

  explicit concrete_symbol_tablet(const symbol_tablet &other)
    : symbol_tablet(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map),
      internal_symbols(other.symbols),
      internal_symbol_base_map(other.symbol_base_map),
      internal_symbol_module_map(other.symbol_module_map)
  {
  }

  concrete_symbol_tablet &operator=(const symbol_tablet &other)
  {
    // Copy to temp and then call move assignment
    return *this=concrete_symbol_tablet(other);
  }

  concrete_symbol_tablet(const concrete_symbol_tablet &other)
    : concrete_symbol_tablet(static_cast<const symbol_tablet &>(other))
  {
  }

  concrete_symbol_tablet &operator=(const concrete_symbol_tablet &other)
  {
    // Copy to temp and then call move assignment
    return *this=concrete_symbol_tablet(other);
  }

  concrete_symbol_tablet(concrete_symbol_tablet &&other)
    : symbol_tablet(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map),
      internal_symbols(std::move(other.internal_symbols)),
      internal_symbol_base_map(std::move(other.internal_symbol_base_map)),
      internal_symbol_module_map(std::move(other.symbol_module_map))
  {
  }

  concrete_symbol_tablet &operator=(concrete_symbol_tablet &&other)
  {
    internal_symbols=std::move(other.internal_symbols);
    internal_symbol_base_map=std::move(other.internal_symbol_base_map);
    internal_symbol_module_map=std::move(other.symbol_module_map);
    return *this;
  }

  void swap(concrete_symbol_tablet &other)
  {
    internal_symbols.swap(other.internal_symbols);
    internal_symbol_base_map.swap(other.internal_symbol_base_map);
    internal_symbol_module_map.swap(other.internal_symbol_module_map);
  }

  virtual symbolt *get_writeable(const irep_idt &identifier) override
  {
    // We know internal_symbols is non-const, so it's safe to cast away
    // the constness introduced by lookup_impl.
    return const_cast<symbolt *>(lookup_impl(internal_symbols, identifier));
  }

  virtual std::pair<symbolt &, bool> insert(symbolt symbol) override;

  virtual void erase(const symbolst::const_iterator &entry) override;

  virtual void clear() override
  {
    internal_symbols.clear();
    internal_symbol_base_map.clear();
    internal_symbol_module_map.clear();
  }
};

#endif // CPROVER_UTIL_SYMBOL_TABLE_H

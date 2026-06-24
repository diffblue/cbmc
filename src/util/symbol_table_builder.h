/// Author: Diffblue Ltd.

// \file Contains a symbol table wrapper that keeps track of suffixes
// that have been used for their prefix

#ifndef CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H
#define CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H

#include "symbol_table_base.h"

/// Wrapper around a symbol table. The fast next-unused-suffix computation
/// (a per-prefix hint cache) is inherited from \ref symbol_table_baset; this
/// wrapper only forwards mutating operations to the wrapped table and resets
/// that cache on clear().
class symbol_table_buildert : public symbol_table_baset
{
private:
  symbol_table_baset &base_symbol_table;

public:
  explicit symbol_table_buildert(symbol_table_baset &base_symbol_table)
    : symbol_table_baset(
        base_symbol_table.symbols,
        base_symbol_table.symbol_base_map,
        base_symbol_table.symbol_module_map),
      base_symbol_table(base_symbol_table)
  {
  }

  symbol_table_buildert(symbol_table_buildert &&other)
    : symbol_table_baset(
        other.symbols,
        other.symbol_base_map,
        other.symbol_module_map),
      base_symbol_table(other.base_symbol_table)
  {
  }

  symbol_table_buildert(const symbol_table_buildert &) = delete;
  symbol_table_buildert &operator=(const symbol_table_buildert &) = delete;
  symbol_table_buildert &operator=(symbol_table_buildert &&) = delete;

  static symbol_table_buildert wrap(symbol_table_baset &base_symbol_table)
  {
    return symbol_table_buildert(base_symbol_table);
  }

  const symbol_tablet &get_symbol_table() const override
  {
    return base_symbol_table.get_symbol_table();
  }

  void erase(const symbolst::const_iterator &entry) override
  {
    base_symbol_table.erase(entry);
  }

  void clear() override
  {
    base_symbol_table.clear();
    suffix_hint_cache.clear();
  }

  bool move(symbolt &symbol, symbolt *&new_symbol) override
  {
    return base_symbol_table.move(symbol, new_symbol);
  }

  symbolt *get_writeable(const irep_idt &identifier) override
  {
    return base_symbol_table.get_writeable(identifier);
  }

  std::pair<symbolt &, bool> insert(symbolt symbol) override
  {
    return base_symbol_table.insert(std::move(symbol));
  }

  iteratort begin() override
  {
    return base_symbol_table.begin();
  }

  iteratort end() override
  {
    return base_symbol_table.end();
  }

  using symbol_table_baset::begin;
  using symbol_table_baset::end;

  void validate(
    const validation_modet vm = validation_modet::INVARIANT) const override
  {
    base_symbol_table.validate(vm);
  }
};

#endif // CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H

/// Author: Diffblue Ltd.

// \file Contains a symbol table wrapper that keeps track of suffixes
// that have been used for their prefix

#ifndef CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H
#define CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H

#include "symbol_table_base.h"

/// Wrapper around a symbol table that keeps track of suffixes for faster
/// calculation of the smallest unused suffix.
class symbol_table_buildert : public symbol_table_baset
{
private:
  symbol_table_baset &base_symbol_table;
  mutable std::map<std::string, std::size_t> next_free_suffix_for_prefix;

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
  symbol_table_buildert &operator=(symbol_table_buildert &&) = default;

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
    next_free_suffix_for_prefix.clear();
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

  /// Try to find the next free identity for the passed-in prefix in
  /// this symbol table.
  /// \remark
  ///     This method needs to generate names deterministically in regards
  ///     to operations that generate the same prefix (and any other operation
  ///     shouldn't affect this).
  ///
  ///     Due to this requirement we don't do anything fancy in regards to
  ///     attempting to find the absolute earliest free suffix if one has been
  ///     deleted, only the next free increment from our last stored value.
  std::size_t next_unused_suffix(const std::string &prefix) const override
  {
    // Check if we have an entry for this particular suffix, if not,
    // create baseline.
    auto suffix_iter = next_free_suffix_for_prefix.insert({prefix, 0}).first;
    std::size_t free_suffix =
      base_symbol_table.next_unused_suffix(prefix, suffix_iter->second);
    suffix_iter->second = free_suffix + 1;
    return free_suffix;
  }
};

#endif // CPROVER_UTIL_SYMBOL_TABLE_BUILDER_H

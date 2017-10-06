// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// A symbol table that records which entries have been updated

#ifndef CPROVER_UTIL_RECORDING_SYMBOL_TABLE_H
#define CPROVER_UTIL_RECORDING_SYMBOL_TABLE_H

#include <utility>
#include <unordered_set>
#include "irep.h"
#include "symbol_table.h"


/// \brief A symbol table that records which entries have been updated/removed
/// \ingroup gr_symbol_table
class recording_symbol_tablet:public symbol_tablet
{
public:
  typedef std::unordered_set<irep_idt, irep_id_hash> changesett;
private:
  symbol_tablet &base_symbol_table;
  // Symbols originally in the table will never be marked inserted
  changesett inserted;
  // get_writeable marks an existing symbol updated
  // Inserted symbols are marked updated, removed ones aren't
  changesett updated;
  // Symbols not originally in the table will never be marked removed
  changesett removed;

private:
  explicit recording_symbol_tablet(symbol_tablet &base_symbol_table)
    : symbol_tablet(
        base_symbol_table.symbols,
        base_symbol_table.symbol_base_map,
        base_symbol_table.symbol_module_map),
      base_symbol_table(base_symbol_table)
  {
  }

public:
  recording_symbol_tablet(const recording_symbol_tablet &other)
    : symbol_tablet(
        other.base_symbol_table.symbols,
        other.base_symbol_table.symbol_base_map,
        other.base_symbol_table.symbol_module_map),
      base_symbol_table(other.base_symbol_table)
  {
  }

  static recording_symbol_tablet wrap(symbol_tablet &base_symbol_table)
  {
    return recording_symbol_tablet(base_symbol_table);
  }

  virtual opt_symbol_reft get_writeable(const irep_idt &identifier) override
  {
    opt_symbol_reft result=base_symbol_table.get_writeable(identifier);
    if(result)
      on_update(identifier);
    return result;
  }

  virtual std::pair<symbolt &, bool> insert(symbolt symbol) override
  {
    std::pair<symbolt &, bool> result=
      base_symbol_table.insert(std::move(symbol));
    if(result.second)
      on_insert(result.first.name);
    return result;
  }

  virtual void erase(const symbolst::const_iterator &entry) override
  {
    base_symbol_table.erase(entry);
    on_remove(entry->first);
  }

  virtual void clear() override
  {
    for(const auto &named_symbol : base_symbol_table.symbols)
      on_remove(named_symbol.first);
    base_symbol_table.clear();
  }

  const changesett &get_inserted() const { return inserted; }
  const changesett &get_updated() const { return updated; }
  const changesett &get_removed() const { return removed; }

private:
  void on_insert(const irep_idt &id)
  {
    if(removed.erase(id)==0)
      inserted.insert(id);
    updated.insert(id);
  }

  void on_update(const irep_idt &id)
  {
    updated.insert(id);
  }

  void on_remove(const irep_idt &id)
  {
    if(inserted.erase(id)==0)
      removed.insert(id);
    updated.erase(id);
  }
};

#endif // CPROVER_UTIL_RECORDING_SYMBOL_TABLE_H

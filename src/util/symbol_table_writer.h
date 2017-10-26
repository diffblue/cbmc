
// Copyright 2016-2017 DiffBlue Limited. All Rights Reserved.

/// \file
/// A symbol table writer that records which entries have been updated

#ifndef CPROVER_UTIL_SYMBOL_TABLE_WRITER_H
#define CPROVER_UTIL_SYMBOL_TABLE_WRITER_H

#include <utility>
#include <unordered_set>
#include "irep.h"
#include "symbol_table.h"

/// \brief A symbol table wrapper that records which entries have been
/// updated/removed
/// \ingroup gr_symbol_table
/// A caller can pass a `journalling_symbol_table_writert` into a callee that is
/// expected to mutate it somehow, then after it has run inspect the recording
/// table's journal to determine what has changed more cheaply than examining
/// every symbol.
///
/// Example of usage:
/// ```
/// symbol_tablet real_table;
/// init_table(real_table);
///
/// journalling_symbol_table_writert journal(actual_table); // Wraps real_table
/// alter_table(journal);

/// for(const auto &added : journal.added())
/// {
///   printf("%s was added\n", added.name);
/// }
class journalling_symbol_table_writert
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
  explicit journalling_symbol_table_writert(symbol_tablet &base_symbol_table):
    base_symbol_table(base_symbol_table)
  {
  }

public:
  journalling_symbol_table_writert(
    const journalling_symbol_table_writert &other)=delete;

  journalling_symbol_table_writert(journalling_symbol_table_writert &&other)
  : base_symbol_table(other.base_symbol_table),
    inserted(std::move(other.inserted)),
    updated(std::move(other.updated)),
    removed(std::move(other.removed))
  {
  }

  /// Permits implicit cast to const symbol_tablet &
  operator const symbol_tablet &() const
  {
    return base_symbol_table;
  }

  static journalling_symbol_table_writert wrap(
    symbol_tablet &base_symbol_table)
  {
    return journalling_symbol_table_writert(base_symbol_table);
  }

  bool add(const symbolt &symbol)
  {
    bool ret=base_symbol_table.add(symbol);
    if(!ret)
      on_insert(symbol.name);
    return ret;
  }

  bool move(symbolt &symbol, symbolt *&new_symbol)
  {
    bool ret=base_symbol_table.move(symbol, new_symbol);
    if(!ret)
      on_insert(symbol.name);
    else
      on_update(symbol.name);
    return ret;
  }

  symbolt *get_writeable(const irep_idt &identifier)
  {
    symbolt *result=base_symbol_table.get_writeable(identifier);
    if(result)
      on_update(identifier);
    return result;
  }

  symbolt &get_writeable_ref(const irep_idt &identifier)
  {
    // Run on_update *after* the get-ref operation in case it throws
    symbolt &result=base_symbol_table.get_writeable_ref(identifier);
    on_update(identifier);
    return result;
  }

  std::pair<symbolt &, bool> insert(symbolt symbol)
  {
    std::pair<symbolt &, bool> result=
      base_symbol_table.insert(std::move(symbol));
    if(result.second)
      on_insert(result.first.name);
    return result;
  }

  bool remove(const irep_idt &id)
  {
    bool ret=base_symbol_table.remove(id);
    if(!ret)
      on_remove(id);
    return ret;
  }

  void erase(const symbol_tablet::symbolst::const_iterator &entry)
  {
    const irep_idt entry_name=entry->first;
    base_symbol_table.erase(entry);
    on_remove(entry_name);
  }

  void clear()
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

#endif // CPROVER_UTIL_SYMBOL_TABLE_WRITER_H

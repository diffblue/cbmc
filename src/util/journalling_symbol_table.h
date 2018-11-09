/// Author: Diffblue Ltd.

/// \file
/// A symbol table writer that records which entries have been updated

#ifndef CPROVER_UTIL_JOURNALLING_SYMBOL_TABLE_H
#define CPROVER_UTIL_JOURNALLING_SYMBOL_TABLE_H

#include <utility>
#include <unordered_set>
#include "irep.h"
#include "symbol_table.h"

/// \brief A symbol table wrapper that records which entries have been
/// updated/removed
/// \ingroup gr_symbol_table
/// A caller can pass a `journalling_symbol_tablet` into a callee that is
/// expected to mutate it somehow, then after it has run inspect the recording
/// table's journal to determine what has changed more cheaply than examining
/// every symbol.
///
/// Example of usage:
/// ```
/// symbol_tablet real_table;
/// init_table(real_table);
///
/// journalling_symbol_tablet journal(actual_table); // Wraps real_table
/// alter_table(journal);
///
/// for(const auto &added : journal.added())
/// {
///   printf("%s was added\n", added.name);
/// }
/// ```
class journalling_symbol_tablet : public symbol_table_baset
{
public:
  typedef std::unordered_set<irep_idt> changesett;

private:
  symbol_table_baset &base_symbol_table;
  // Symbols originally in the table will never be marked inserted
  changesett inserted;
  // get_writeable marks an existing symbol updated
  // Inserted symbols are marked updated, removed ones aren't
  changesett updated;
  // Symbols not originally in the table will never be marked removed
  changesett removed;

private:
  explicit journalling_symbol_tablet(symbol_table_baset &base_symbol_table)
    : symbol_table_baset(
        base_symbol_table.symbols,
        base_symbol_table.symbol_base_map,
        base_symbol_table.symbol_module_map),
      base_symbol_table(base_symbol_table)
  {
  }

public:
  journalling_symbol_tablet(const journalling_symbol_tablet &other) = delete;

  journalling_symbol_tablet(journalling_symbol_tablet &&other)
    : symbol_table_baset(
        other.symbols,
        other.symbol_base_map,
        other.symbol_module_map),
      base_symbol_table(other.base_symbol_table),
      inserted(std::move(other.inserted)),
      updated(std::move(other.updated)),
      removed(std::move(other.removed))
  {
  }

  virtual const symbol_tablet &get_symbol_table() const override
  {
    return base_symbol_table.get_symbol_table();
  }

  static journalling_symbol_tablet wrap(symbol_table_baset &base_symbol_table)
  {
    return journalling_symbol_tablet(base_symbol_table);
  }

  virtual bool move(symbolt &symbol, symbolt *&new_symbol) override
  {
    bool ret = base_symbol_table.move(symbol, new_symbol);
    if(!ret)
      on_insert(symbol.name);
    else
      on_update(symbol.name);
    return ret;
  }

  virtual symbolt *get_writeable(const irep_idt &identifier) override
  {
    symbolt *result = base_symbol_table.get_writeable(identifier);
    if(result)
      on_update(identifier);
    return result;
  }

  std::size_t next_unused_suffix(const std::string &prefix) const override
  {
    return base_symbol_table.next_unused_suffix(prefix);
  }

  virtual std::pair<symbolt &, bool> insert(symbolt symbol) override
  {
    std::pair<symbolt &, bool> result =
      base_symbol_table.insert(std::move(symbol));
    if(result.second)
      on_insert(result.first.name);
    return result;
  }

  virtual void
  erase(const symbol_tablet::symbolst::const_iterator &entry) override
  {
    const irep_idt entry_name = entry->first;
    base_symbol_table.erase(entry);
    on_remove(entry_name);
  }

  virtual void clear() override
  {
    for(const auto &named_symbol : base_symbol_table.symbols)
      on_remove(named_symbol.first);
    base_symbol_table.clear();
  }

  virtual iteratort begin() override
  {
    return iteratort(
      base_symbol_table.begin(), [this](const irep_idt &id) { on_update(id); });
  }
  virtual iteratort end() override
  {
    return iteratort(
      base_symbol_table.end(), [this](const irep_idt &id) { on_update(id); });
  }

  const changesett &get_inserted() const
  {
    return inserted;
  }
  const changesett &get_updated() const
  {
    return updated;
  }
  const changesett &get_removed() const
  {
    return removed;
  }

private:
  void on_insert(const irep_idt &id)
  {
    if(removed.erase(id) == 0)
      inserted.insert(id);
    updated.insert(id);
  }

  void on_update(const irep_idt &id)
  {
    updated.insert(id);
  }

  void on_remove(const irep_idt &id)
  {
    if(inserted.erase(id) == 0)
      removed.insert(id);
    updated.erase(id);
  }
};

#endif // CPROVER_UTIL_JOURNALLING_SYMBOL_TABLE_H

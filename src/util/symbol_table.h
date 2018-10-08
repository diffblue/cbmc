/// Author: Diffblue Ltd.

/// \file
/// Symbol table

#ifndef CPROVER_UTIL_SYMBOL_TABLE_H
#define CPROVER_UTIL_SYMBOL_TABLE_H

#include "symbol_table_base.h"

#define forall_symbol_base_map(it, expr, base_name) \
  for(symbol_base_mapt::const_iterator it=(expr).lower_bound(base_name), \
                                       it_end=(expr).upper_bound(base_name); \
      it!=it_end; ++it)


/// \brief The symbol table
/// \ingroup gr_symbol_table
class symbol_tablet : public symbol_table_baset
{
private:
  symbolst internal_symbols;
  symbol_base_mapt internal_symbol_base_map;
  symbol_module_mapt internal_symbol_module_map;

public:
  symbol_tablet()
    : symbol_table_baset(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map)
  {
  }

  symbol_tablet(const symbol_tablet &other)
    : symbol_table_baset(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map),
      internal_symbols(other.internal_symbols),
      internal_symbol_base_map(other.internal_symbol_base_map),
      internal_symbol_module_map(other.internal_symbol_module_map)
  {
  }

  symbol_tablet &operator=(const symbol_tablet &other)
  {
    // Copy to temp and then call move assignment
    return *this=symbol_tablet(other);
  }

  symbol_tablet(symbol_tablet &&other)
    : symbol_table_baset(
        internal_symbols,
        internal_symbol_base_map,
        internal_symbol_module_map),
      internal_symbols(std::move(other.internal_symbols)),
      internal_symbol_base_map(std::move(other.internal_symbol_base_map)),
      internal_symbol_module_map(std::move(other.internal_symbol_module_map))
  {
  }

  symbol_tablet &operator=(symbol_tablet &&other)
  {
    internal_symbols = std::move(other.internal_symbols);
    internal_symbol_base_map = std::move(other.internal_symbol_base_map);
    internal_symbol_module_map = std::move(other.internal_symbol_module_map);
    return *this;
  }

  void swap(symbol_tablet &other)
  {
    internal_symbols.swap(other.internal_symbols);
    internal_symbol_base_map.swap(other.internal_symbol_base_map);
    internal_symbol_module_map.swap(other.internal_symbol_module_map);
  }

public:
  virtual const symbol_tablet &get_symbol_table() const override
  {
    return *this;
  }

  /// Find a symbol in the symbol table for read-write access.
  /// \param name: The name of the symbol to look for
  /// \return a pointer to the found symbol if it exists, nullptr otherwise.
  virtual symbolt *get_writeable(const irep_idt &name) override
  {
    symbolst::iterator it = internal_symbols.find(name);
    return it != internal_symbols.end() ? &it->second : nullptr;
  }

  virtual std::pair<symbolt &, bool> insert(symbolt symbol) override;
  virtual bool move(symbolt &symbol, symbolt *&new_symbol) override;

  virtual void erase(const symbolst::const_iterator &entry) override;
  virtual void clear() override
  {
    internal_symbols.clear();
    internal_symbol_base_map.clear();
    internal_symbol_module_map.clear();
  }

  virtual iteratort begin() override
  {
    return iteratort(internal_symbols.begin());
  }
  virtual iteratort end() override
  {
    return iteratort(internal_symbols.end());
  }

  /// Check that the symbol table is well-formed
  void validate() const
  {
  }
};

#endif // CPROVER_UTIL_SYMBOL_TABLE_H

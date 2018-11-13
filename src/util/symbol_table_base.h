/// Author: Diffblue Ltd.

/// \file
/// Symbol table base class interface

#ifndef CPROVER_UTIL_SYMBOL_TABLE_BASE_H
#define CPROVER_UTIL_SYMBOL_TABLE_BASE_H

#include <map>
#include <unordered_map>

#include "symbol.h"

typedef std::multimap<irep_idt, irep_idt> symbol_base_mapt;
typedef std::multimap<irep_idt, irep_idt> symbol_module_mapt;

class symbol_tablet;

/// \brief The symbol table base class interface
/// \ingroup gr_symbol_table
class symbol_table_baset
{
public:
  typedef std::unordered_map<irep_idt, symbolt> symbolst;

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

  virtual ~symbol_table_baset();

public:
  /// Permits implicit cast to const symbol_tablet &
  operator const symbol_tablet &() const
  {
    return get_symbol_table();
  }
  virtual const symbol_tablet &get_symbol_table() const = 0;

  /// Check whether a symbol exists in the symbol table
  /// \param name: The name of the symbol to look for
  /// \return True if the symbol exists
  bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name) != symbols.end();
  }

  /// Find a symbol in the symbol table for read-only access.
  /// \param name: The name of the symbol to look for
  /// \return A pointer to the found symbol if it exists, nullptr otherwise.
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
  /// \return A pointer to the found symbol if it exists, nullptr otherwise.
  virtual symbolt *get_writeable(const irep_idt &name) = 0;

  /// Find a symbol in the symbol table for read-write access.
  /// \param name: The name of the symbol to look for.
  /// \return A reference to the symbol.
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
  ///   moved or copied in.
  /// \return: Returns a reference to the newly inserted symbol or to the
  ///   existing symbol if a symbol with the same name already exists in the
  ///   symbol table, along with a bool that is true if a new symbol was
  ///   inserted.
  virtual std::pair<symbolt &, bool> insert(symbolt symbol) = 0;
  virtual bool move(symbolt &symbol, symbolt *&new_symbol) = 0;

  bool remove(const irep_idt &name);
  /// Remove a symbol from the symbol table
  /// \param entry: an iterator pointing at the symbol to remove
  virtual void erase(const symbolst::const_iterator &entry) = 0;
  virtual void clear() = 0;

  void show(std::ostream &out) const;

  class iteratort
  {
  private:
    symbolst::iterator it;
    std::function<void(const irep_idt &id)> on_get_writeable;

  public:
    explicit iteratort(symbolst::iterator it) : it(std::move(it))
    {
    }

    iteratort(
        const iteratort &it,
        std::function<void(const irep_idt &id)> on_get_writeable)
      : it(it.it), on_get_writeable(std::move(on_get_writeable))
    {
    }

    // The following typedefs are NOLINT as they are needed by the STL
    typedef symbolst::iterator::difference_type difference_type;     // NOLINT
    typedef symbolst::const_iterator::value_type value_type;         // NOLINT
    typedef symbolst::const_iterator::pointer pointer;               // NOLINT
    typedef symbolst::const_iterator::reference reference;           // NOLINT
    typedef symbolst::iterator::iterator_category iterator_category; // NOLINT

    bool operator!=(const iteratort &other) const
    {
      return it != other.it;
    }

    bool operator==(const iteratort &other) const
    {
      return it == other.it;
    }

    /// Preincrement operator
    /// Do not call on the end() iterator
    iteratort &operator++()
    {
      ++it;
      return *this;
    }

    /// Post-increment operator
    /// \remarks Expensive copy. Avoid if possible.
    iteratort operator++(int)
    {
      iteratort copy(*this);
      this->operator++();
      return copy;
    }

    /// Dereference operator
    /// \remarks Dereferencing end() iterator is undefined behaviour
    reference operator*() const
    {
      return *it;
    }

    /// Dereference operator (member access)
    /// \remarks Dereferencing end() iterator is undefined behaviour
    pointer operator->() const
    {
      return &**this;
    }

    /// Whereas the dereference operator gives a constant reference to the
    /// current symbol, this method allows users to get a writeable reference
    /// to the symbol.
    /// \remarks This method calls the on_get_writeable method first to give
    ///   derived symbol table classes the opportunity to note that this
    ///   symbol is being written to before it is accessed.
    /// \return A non-const reference to the current symbol.
    symbolt &get_writeable_symbol()
    {
      if(on_get_writeable)
        on_get_writeable((*this)->first);
      return it->second;
    }
  };

  virtual iteratort begin() = 0;
  virtual iteratort end() = 0;
};

std::ostream &
operator<<(std::ostream &out, const symbol_table_baset &symbol_table);

#endif // CPROVER_UTIL_SYMBOL_TABLE_BASE_H

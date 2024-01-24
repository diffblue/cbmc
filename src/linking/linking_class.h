/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Linking

#ifndef CPROVER_LINKING_LINKING_CLASS_H
#define CPROVER_LINKING_LINKING_CLASS_H

#include <util/namespace.h>
#include <util/rename_symbol.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "casting_replace_symbol.h"

#include <unordered_set>

class message_handlert;

class linkingt
{
public:
  linkingt(
    symbol_table_baset &_main_symbol_table,
    message_handlert &_message_handler)
    : main_symbol_table(_main_symbol_table),
      ns(_main_symbol_table),
      message_handler(_message_handler)
  {
  }

  /// Merges the symbol table \p src_symbol_table into `main_symbol_table`,
  /// renaming symbols from \p src_symbol_table when necessary.
  /// \return True, iff linking failed with unresolvable conflicts.
  bool link(const symbol_table_baset &src_symbol_table);

  rename_symbolt rename_main_symbol, rename_new_symbol;
  casting_replace_symbolt object_type_updates;

protected:
  enum renamingt
  {
    NO_RENAMING,
    RENAME_OLD,
    RENAME_NEW
  };

  renamingt
  needs_renaming_type(const symbolt &old_symbol, const symbolt &new_symbol);

  renamingt
  needs_renaming_non_type(const symbolt &old_symbol, const symbolt &new_symbol);

  renamingt needs_renaming(const symbolt &old_symbol, const symbolt &new_symbol)
  {
    if(new_symbol.is_type)
      return needs_renaming_type(old_symbol, new_symbol);
    else
      return needs_renaming_non_type(old_symbol, new_symbol);
  }

  std::unordered_map<irep_idt, irep_idt> rename_symbols(
    const symbol_table_baset &,
    const std::unordered_set<irep_idt> &needs_to_be_renamed);
  void copy_symbols(
    const symbol_table_baset &,
    const std::unordered_map<irep_idt, irep_idt> &);

  void duplicate_non_type_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void duplicate_code_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void duplicate_object_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);

  bool adjust_object_type(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    bool &set_to_new);

  struct adjust_type_infot
  {
    adjust_type_infot(
      const symbolt &_old_symbol,
      const symbolt &_new_symbol):
      old_symbol(_old_symbol),
      new_symbol(_new_symbol),
      set_to_new(false)
    {
    }

    const symbolt &old_symbol;
    const symbolt &new_symbol;
    bool set_to_new;
    std::unordered_set<irep_idt> o_symbols;
    std::unordered_set<irep_idt> n_symbols;
  };

  bool adjust_object_type_rec(
    const typet &type1,
    const typet &type2,
    adjust_type_infot &info);

  void duplicate_type_symbol(
    symbolt &old_symbol,
    const symbolt &new_symbol);

  symbol_table_baset &main_symbol_table;
  namespacet ns;
  message_handlert &message_handler;

  irep_idt rename(const symbol_table_baset &, const irep_idt &);

  // the new IDs created by renaming
  std::unordered_set<irep_idt> renamed_ids;
};

#endif // CPROVER_LINKING_LINKING_CLASS_H

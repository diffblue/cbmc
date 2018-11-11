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
#include <util/replace_symbol.h>
#include <util/typecheck.h>
#include <util/std_expr.h>

class casting_replace_symbolt : public replace_symbolt
{
private:
  bool replace_symbol_expr(symbol_exprt &dest) const override;
};

class linkingt:public typecheckt
{
public:
  linkingt(
    symbol_tablet &_main_symbol_table,
    symbol_tablet &_src_symbol_table,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    main_symbol_table(_main_symbol_table),
    src_symbol_table(_src_symbol_table),
    ns(_main_symbol_table)
  {
  }

  virtual void typecheck();

  rename_symbolt rename_symbol;
  casting_replace_symbolt object_type_updates;

protected:
  bool needs_renaming_type(
    const symbolt &old_symbol,
    const symbolt &new_symbol);

  bool needs_renaming_non_type(
    const symbolt &old_symbol,
    const symbolt &new_symbol);

  bool needs_renaming(
    const symbolt &old_symbol,
    const symbolt &new_symbol)
  {
    if(new_symbol.is_type)
      return needs_renaming_type(old_symbol, new_symbol);
    else
      return needs_renaming_non_type(old_symbol, new_symbol);
  }

  void do_type_dependencies(std::unordered_set<irep_idt> &);

  void rename_symbols(const std::unordered_set<irep_idt> &needs_to_be_renamed);
  void copy_symbols();

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

  std::string expr_to_string(
    const irep_idt &identifier,
    const exprt &expr) const;

  std::string type_to_string(
    const irep_idt &identifier,
    const typet &type) const;

  std::string type_to_string_verbose(
    const symbolt &symbol,
    const typet &type) const;

  std::string type_to_string_verbose(
    const symbolt &symbol) const
  {
    return type_to_string_verbose(symbol, symbol.type);
  }

  void detailed_conflict_report_rec(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const typet &type1,
    const typet &type2,
    unsigned depth,
    exprt &conflict_path);

  void detailed_conflict_report(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const typet &type1,
    const typet &type2)
  {
    symbol_exprt conflict_path(ID_C_this);
    detailed_conflict_report_rec(
      old_symbol,
      new_symbol,
      type1,
      type2,
      10, // somewhat arbitrary limit
      conflict_path);
  }

  void link_error(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg);

  void link_warning(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg);

  void show_struct_diff(
    const struct_typet &old_type,
    const struct_typet &new_type);

  symbol_tablet &main_symbol_table;
  symbol_tablet &src_symbol_table;

  namespacet ns;

  // X -> Y iff Y uses X for new symbol type IDs X and Y
  typedef std::unordered_map<irep_idt, std::unordered_set<irep_idt>> used_byt;

  irep_idt rename(irep_idt);

  // the new IDs created by renaming
  std::unordered_set<irep_idt> renamed_ids;
};

#endif // CPROVER_LINKING_LINKING_CLASS_H

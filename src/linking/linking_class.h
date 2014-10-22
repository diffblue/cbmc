/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_LINKING_CLASS_H
#define CPROVER_LINKING_LINKING_CLASS_H

#include <util/namespace.h>
#include <util/rename_symbol.h>
#include <util/hash_cont.h>
#include <util/typecheck.h>

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
 
protected:

  typedef hash_set_cont<irep_idt, irep_id_hash> id_sett;

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

  void do_type_dependencies(id_sett &);
    
  void rename_symbols(const id_sett &needs_to_be_renamed);
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
  
  void duplicate_type_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);
  
  std::string expr_to_string(
    const namespacet &ns,
    const irep_idt &identifier,
    const exprt &expr) const;

  std::string type_to_string(
    const namespacet &ns,
    const irep_idt &identifier,
    const typet &type) const;

  std::string type_to_string_verbose(
    const namespacet &ns,
    const symbolt &symbol,
    const typet &type) const;

  std::string type_to_string_verbose(
    const namespacet &ns,
    const symbolt &symbol) const
  {
    return type_to_string_verbose(ns, symbol, symbol.type);
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
  typedef hash_map_cont<irep_idt, id_sett, irep_id_hash> used_byt;

  irep_idt rename(irep_idt);

  // the new IDs created by renaming  
  id_sett renamed_ids;
};

#endif

/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_LINKING_CLASS_H
#define CPROVER_LINKING_LINKING_CLASS_H

#include <util/namespace.h>
#include <util/replace_symbol.h>
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
    ns(_main_symbol_table),
    renaming_counter(0)
  {
  }
   
  virtual void typecheck();
  
  replace_symbolt replace_symbol;
 
protected:
  void duplicate_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void duplicate_type_symbol(
    symbolt &old_symbol, 
    symbolt &new_symbol,
    bool &move);

  void duplicate_non_type_symbol(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void rename_type_symbol(symbolt &new_symbol);

  void inspect_src_symbol(const irep_idt &identifier);
  
  irep_idt rename(const irep_idt &old_identifier);

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

  symbol_tablet &main_symbol_table;
  symbol_tablet &src_symbol_table;
  namespacet ns;
  
  unsigned renaming_counter;
  
  typedef hash_set_cont<irep_idt, irep_id_hash> id_sett;
  id_sett processing, completed;
};

#endif

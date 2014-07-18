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
    ns(_main_symbol_table)
  {
  }
   
  virtual void typecheck();
  
  replace_symbolt replace_symbol;
 
protected:
  bool is_different_type(
    const symbolt &old_symbol,
    const symbolt &new_symbol);
    
  void do_type_symbols();
  void do_non_type_symbols();
  
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

  typedef hash_set_cont<irep_idt, irep_id_hash> id_sett;

  // X -> Y iff Y uses X for new symbol type IDs X and Y
  typedef hash_map_cont<irep_idt, id_sett, irep_id_hash> used_byt;
  used_byt used_by;
  
  void compute_used_by();
  void rename_type(irep_idt);
};

#endif

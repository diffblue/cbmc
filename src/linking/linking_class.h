/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_LINK_CLASS_H
#define CPROVER_ANSI_C_C_LINK_CLASS_H

#include <namespace.h>
#include <replace_symbol.h>
#include <hash_cont.h>
#include <typecheck.h>

class linkingt:public typecheckt
{
public:
  linkingt(
    contextt &_main_context,
    contextt &_src_context,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    main_context(_main_context),
    src_context(_src_context),
    ns(_main_context, _src_context), // order matters
    renaming_counter(0)
  {
  }
   
  virtual void typecheck();
  
  replace_symbolt replace_symbol;
 
protected:
  void duplicate(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void duplicate_type(
    symbolt &old_symbol, 
    symbolt &new_symbol);

  void duplicate_non_type(
    symbolt &old_symbol,
    symbolt &new_symbol);

  void inspect_src_symbol(const irep_idt &identifier);
  
  irep_idt rename(const irep_idt &old_identifier);

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  contextt &main_context;
  contextt &src_context;
  namespacet ns;
  
  unsigned renaming_counter;
  
  typedef hash_set_cont<irep_idt, irep_id_hash> processingt;
  processingt processing;
};

#endif

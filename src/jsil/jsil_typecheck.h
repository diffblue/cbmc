/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_JSIL_TYPECHECK_H
#define CPROVER_JSIL_TYPECHECK_H

#include <util/typecheck.h>
#include <util/namespace.h>

class codet;

bool jsil_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

bool jsil_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class jsil_typecheckt:public typecheckt
{
public:
  jsil_typecheckt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    symbol_table(_symbol_table),
    ns(symbol_table)
  {
  }

  virtual ~jsil_typecheckt() { }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr) {};

protected:
  symbol_tablet &symbol_table;
  const namespacet ns;

  void typecheck_type_symbol(symbolt &symbol) {};
  void typecheck_non_type_symbol(symbolt &symbol);
  void typecheck_code(codet &code);
  void typecheck_type(typet &type) {};
#if 0
  void typecheck_expr_symbol(symbol_exprt &expr);
  void typecheck_expr_member(member_exprt &expr);
  void typecheck_expr_java_new(side_effect_exprt &expr);
  void typecheck_expr_java_new_array(side_effect_exprt &expr);
#endif

  // overload to use language-specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  hash_set_cont<irep_idt, irep_id_hash> already_typechecked;
};

#endif


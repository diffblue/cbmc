/*******************************************************************\

Module: JAVA Bytecode Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_TYPECHECK_H
#define CPROVER_JAVA_BYTECODE_TYPECHECK_H

#include <set>

#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

bool java_bytecode_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

bool java_bytecode_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class java_bytecode_typecheckt:public typecheckt
{
public:
  java_bytecode_typecheckt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    symbol_table(_symbol_table),
    ns(symbol_table)
  {
  }

  virtual ~java_bytecode_typecheckt() { }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);
  
protected:
  symbol_tablet &symbol_table;
  const namespacet ns;

  void typecheck_type_symbol(symbolt &symbol);
  void typecheck_non_type_symbol(symbolt &symbol);
  void typecheck_code(codet &code);
  void typecheck_type(typet &type);
  void typecheck_expr_symbol(symbol_exprt &expr);
  void typecheck_expr_member(member_exprt &expr);
  void typecheck_expr_java_new(side_effect_exprt &expr);
  void typecheck_expr_java_new_array(side_effect_exprt &expr);

  // overload to use language-specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);
  
  std::set<irep_idt> already_typechecked;
};

#endif


/*******************************************************************\

Module: JAVA Bytecode Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_TYPECHECK_H
#define CPROVER_JAVA_BYTECODE_TYPECHECK_H

#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

bool java_bytecode_typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

bool java_bytecode_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class java_bytecode_typecheckt:
  public typecheckt,
  public namespacet
{
public:
  java_bytecode_typecheckt(
    symbol_tablet &_symbol_table,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    namespacet(_symbol_table),
    src_symbol_table(_symbol_table),
    ns(dest_symbol_table),
    module(_module),
    mode(ID_java)
  {
  }

  virtual ~java_bytecode_typecheckt() { }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);
  
protected:
  symbol_tablet &src_symbol_table;
  symbol_tablet dest_symbol_table;
  const namespacet ns;
  const irep_idt module;
  const irep_idt mode;

  void typecheck_symbol(symbolt &symbol);
  void typecheck_code(codet &code);
  void typecheck_type(typet &type);
  void typecheck_expr_symbol(symbol_exprt &expr);
  void typecheck_expr_java_new(side_effect_exprt &expr);

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);
};

#endif


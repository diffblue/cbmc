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

#include "java_bytecode_parse_tree.h"

bool java_bytecode_typecheck(
  java_bytecode_parse_treet &parse_tree,
  symbol_tablet &context,
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
    java_bytecode_parse_treet &_parse_tree,
    symbol_tablet &_context,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    namespacet(_context),
    parse_tree(_parse_tree),
    context(_context),
    module(_module),
    mode("JAVA")
  {
  }

  java_bytecode_typecheckt(
    java_bytecode_parse_treet &_parse_tree,
    symbol_tablet &_context1,
    const symbol_tablet &_context2,
    const std::string &_module,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    namespacet(_context1, _context2),
    parse_tree(_parse_tree),
    context(_context1),
    module(_module),
    mode("JAVA")
  {
  }

  virtual ~java_bytecode_typecheckt() { }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);

protected:
  java_bytecode_parse_treet &parse_tree;
  symbol_tablet &context;
  const irep_idt module;
  const irep_idt mode;

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  void typecheck_function_body(symbolt &symbol);  
};

#endif


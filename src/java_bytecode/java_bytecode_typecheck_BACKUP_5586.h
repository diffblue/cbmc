/*******************************************************************\

Module: JAVA Bytecode Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_TYPECHECK_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_TYPECHECK_H

#include <set>
#include <map>

#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

bool java_bytecode_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  bool string_refinement_enabled);

bool java_bytecode_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class java_bytecode_typecheckt:public typecheckt
{
public:
<<<<<<< 37f0ac9399d6923b9c41a8eb78358382e8c824b5
  java_bytecode_typecheckt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    bool _string_refinement_enabled):
    typecheckt(_message_handler),
    symbol_table(_symbol_table),
    ns(symbol_table),
    string_refinement_enabled(_string_refinement_enabled)
  {
  }

  virtual ~java_bytecode_typecheckt() { }
=======
  java_bytecode_typecheckt(symbol_tablet &_symbol_table,
                           message_handlert &_message_handler);

  virtual ~java_bytecode_typecheckt() = default;
>>>>>>> Add nondet recursive expansion to typecheck_expr

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);

protected:
  symbol_tablet &symbol_table;
  const namespacet ns;
  bool string_refinement_enabled;

  void typecheck_type_symbol(symbolt &);
  void typecheck_non_type_symbol(symbolt &);
  void typecheck_code(codet &);
  void typecheck_type(typet &);
  void typecheck_expr_symbol(symbol_exprt &);
  void typecheck_expr_java_string_literal(exprt &);
  void typecheck_expr_member(member_exprt &);
  void typecheck_expr_java_new(side_effect_exprt &);
  void typecheck_expr_java_new_array(side_effect_exprt &);

  // overload to use language-specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  std::set<irep_idt> already_typechecked;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_TYPECHECK_H

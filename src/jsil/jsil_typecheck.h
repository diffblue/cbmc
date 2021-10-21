/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_TYPECHECK_H
#define CPROVER_JSIL_JSIL_TYPECHECK_H

#include <unordered_set>

#include <util/namespace.h>
#include <util/typecheck.h>

class code_assignt;
class code_function_callt;
class code_ifthenelset;
class code_frontend_returnt;
class code_try_catcht;
class codet;
class message_handlert;
class side_effect_expr_throwt;
class symbol_exprt;
class symbol_tablet;

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
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : typecheckt(_message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      proc_name()
  {
  }

  virtual ~jsil_typecheckt() { }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);

protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  // prefix to variables which is set in typecheck_declaration
  irep_idt proc_name;

  void update_expr_type(exprt &expr, const typet &type);
  void make_type_compatible(exprt &expr, const typet &type, bool must);
  void typecheck_type_symbol(symbolt &) {}
  void typecheck_non_type_symbol(symbolt &symbol);
  void typecheck_symbol_expr(symbol_exprt &symbol_expr);
  void typecheck_expr_side_effect_throw(side_effect_expr_throwt &expr);
  void typecheck_expr_delete(exprt &expr);
  void typecheck_expr_index(exprt &expr);
  void typecheck_expr_proto_field(exprt &expr);
  void typecheck_expr_proto_obj(exprt &expr);
  void typecheck_expr_has_field(exprt &expr);
  void typecheck_expr_ref(exprt &expr);
  void typecheck_expr_field(exprt &expr);
  void typecheck_expr_base(exprt &expr);
  void typecheck_expr_constant(exprt &expr);
  void typecheck_expr_concatenation(exprt &expr);
  void typecheck_expr_subtype(exprt &expr);
  void typecheck_expr_binary_boolean(exprt &expr);
  void typecheck_expr_binary_arith(exprt &expr);
  void typecheck_exp_binary_equal(exprt &expr);
  void typecheck_expr_binary_compare(exprt &expr);
  void typecheck_expr_unary_boolean(exprt &expr);
  void typecheck_expr_unary_string(exprt &expr);
  void typecheck_expr_unary_num(exprt &expr);
  void typecheck_expr_operands(exprt &expr);
  void typecheck_expr_main(exprt &expr);
  void typecheck_code(codet &code);
  void typecheck_function_call(code_function_callt &function_call);
  void typecheck_return(code_frontend_returnt &);
  void typecheck_block(codet &code);
  void typecheck_ifthenelse(code_ifthenelset &code);
  void typecheck_assign(code_assignt &code);
  void typecheck_try_catch(code_try_catcht &code);
  void typecheck_type(typet &type);
  irep_idt add_prefix(const irep_idt &ds);

  // overload to use language-specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  std::unordered_set<irep_idt> already_typechecked;
};

#endif // CPROVER_JSIL_JSIL_TYPECHECK_H

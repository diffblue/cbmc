/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H

#include "goto_model.h"
#include <util/message.h>
#include <util/expr.h>
#include <util/namespace.h>


class remove_const_function_pointerst:public messaget
{
public:
  typedef std::set<exprt> functionst;
  typedef std::list<exprt> expressionst;
  remove_const_function_pointerst(
    message_handlert &message_handler,
    const exprt &base_expression,
    const namespacet &ns,
    const symbol_tablet &symbol_table);

  bool operator()(functionst &out_functions);

private:
  exprt replace_const_symbols(const exprt &expression) const;
  exprt resolve_symbol(const symbol_exprt &symbol_expr) const;

  // recursive functions for dealing with the function pointer
  bool try_resolve_function_call(const exprt &expr, functionst &out_functions);

  bool try_resolve_index_of_function_call(
    const index_exprt &index_expr, functionst &out_functions);

  // recursive functions for dealing with the auxiliary elements
  bool try_resolve_expression(
    const exprt &expr,
    expressionst &out_resolved_expression,
    bool &out_is_const);

  bool try_resolve_index_value(
    const exprt &index_value_expr, mp_integer &out_array_index);

  bool try_resolve_index_of(
    const index_exprt &index_expr,
    expressionst &out_expressions,
    bool &out_is_const);

  bool is_expression_const(const exprt &expression) const;
  bool is_type_const(const typet &type) const;

  exprt get_component_value(
    const struct_exprt &struct_expr, const member_exprt &member_expr);

  const exprt original_expression;
  const namespacet &ns;
  const symbol_tablet &symbol_table;
};

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H

/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H

#include <list>
#include <unordered_set>

#include <util/expr.h>
#include <util/message.h>
#include <util/mp_arith.h>

class address_of_exprt;
class dereference_exprt;
class index_exprt;
class member_exprt;
class namespacet;
class struct_exprt;
class symbol_exprt;
class symbol_tablet;
class typecast_exprt;

class remove_const_function_pointerst
{
public:
  typedef std::unordered_set<symbol_exprt, irep_hash> functionst;
  typedef std::list<exprt> expressionst;
  remove_const_function_pointerst(
    message_handlert &message_handler,
    const namespacet &ns,
    const symbol_tablet &symbol_table);

  bool operator()(const exprt &base_expression, functionst &out_functions);

private:
  exprt replace_const_symbols(const exprt &expression) const;
  exprt resolve_symbol(const symbol_exprt &symbol_expr) const;

  // recursive functions for dealing with the function pointer
  bool try_resolve_function_call(const exprt &expr, functionst &out_functions);

  bool try_resolve_function_calls(
    const expressionst &exprs, functionst &out_functions);

  bool try_resolve_index_of_function_call(
    const index_exprt &index_expr, functionst &out_functions);

  bool try_resolve_member_function_call(
    const member_exprt &member_expr, functionst &out_functions);

  bool try_resolve_address_of_function_call(
    const address_of_exprt &address_expr, functionst &out_functions);

  bool try_resolve_dereference_function_call(
    const dereference_exprt &deref_expr, functionst &out_functions);

  bool try_resolve_typecast_function_call(
    const typecast_exprt &typecast_expr, functionst &out_functions);

  // recursive functions for dealing with the auxiliary elements
  bool try_resolve_expression(
    const exprt &expr,
    expressionst &out_resolved_expression,
    bool &out_is_const);

  bool try_resolve_index_of(
    const index_exprt &index_expr,
    expressionst &out_expressions,
    bool &out_is_const);

  bool try_resolve_member(
    const member_exprt &member_expr,
    expressionst &out_expressions,
    bool &out_is_const);

  bool try_resolve_dereference(
    const dereference_exprt &deref_expr,
    expressionst &out_expressions,
    bool &out_is_const);

  bool try_resolve_typecast(
    const typecast_exprt &typecast_expr,
    expressionst &out_expressions,
    bool &out_is_const);

  bool is_const_expression(const exprt &expression) const;
  bool is_const_type(const typet &type) const;

  bool try_resolve_index_value(
    const exprt &index_value_expr, mp_integer &out_array_index);

  exprt get_component_value(
    const struct_exprt &struct_expr, const member_exprt &member_expr);

  messaget log;
  const namespacet &ns;
  const symbol_tablet &symbol_table;
};

#define OPT_REMOVE_CONST_FUNCTION_POINTERS \
  "(remove-const-function-pointers)"

#define HELP_REMOVE_CONST_FUNCTION_POINTERS                                    \
  " --remove-const-function-pointers\n"                                        \
  "                              remove function pointers that are constant"   \
  " or constant part of an array\n"

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_CONST_FUNCTION_POINTERS_H

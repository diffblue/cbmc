/*******************************************************************\

Module: Callback object for dereference_rec

Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/

/// \file
/// Callback object for dereference_rec

#ifndef CPROVER_GOTO_SYMEX_SINGLE_VALUE_SET_DEREFERENCE_CALLBACK_H
#define CPROVER_GOTO_SYMEX_SINGLE_VALUE_SET_DEREFERENCE_CALLBACK_H

#include <pointer-analysis/dereference_callback.h>

/// Callback object that \ref goto_symext::dereference_rec provides to
/// \ref value_set_dereferencet to provide value sets (from goto-symex's
/// working value set) and retrieve or create failed symbols on demand.
/// For details of symex-dereference's operation see
/// \ref goto_symext::dereference
class single_value_set_dereference_callbackt : public dereference_callbackt
{
public:
  single_value_set_dereference_callbackt(
    const exprt &query_expr,
    const value_setst::valuest &return_values)
    : query_expr(query_expr), return_values(return_values)
  {
  }

  bool used_correctly();

protected:
  const exprt &query_expr;
  const value_setst::valuest &return_values;
  bool get_or_create_failed_symbol_called = false;
  mutable bool get_value_set_called_with_right_query_expr = false;
  mutable bool get_value_set_called_with_wrong_query_expr = false;

  void get_value_set(const exprt &expr, value_setst::valuest &value_set)
    const override;

  const symbolt *get_or_create_failed_symbol(const exprt &expr) override;
};

#endif // CPROVER_GOTO_SYMEX_SINGLE_VALUE_SET_DEREFERENCE_CALLBACK_H
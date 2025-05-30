/*******************************************************************\

Module: Variant of simplify_exprt that uses a value_sett

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_SIMPLIFY_EXPR_WITH_VALUE_SET_H
#define CPROVER_GOTO_SYMEX_SIMPLIFY_EXPR_WITH_VALUE_SET_H

#include <util/simplify_expr_class.h>

class value_sett;

class simplify_expr_with_value_sett : public simplify_exprt
{
public:
  simplify_expr_with_value_sett(
    const value_sett &_vs,
    const irep_idt &_mode,
    const namespacet &_ns)
    : simplify_exprt(_ns), value_set(_vs), language_mode(_mode)
  {
  }

  [[nodiscard]] resultt<>
  simplify_inequality(const binary_relation_exprt &) override;
  /// When all candidates in the value set have the same offset we can replace a
  /// pointer_offset expression by the offset value found in the value set.
  [[nodiscard]] resultt<>
  simplify_inequality_pointer_object(const binary_relation_exprt &) override;
  [[nodiscard]] resultt<>
  simplify_pointer_offset(const pointer_offset_exprt &) override;

protected:
  const value_sett &value_set;
  const irep_idt language_mode;
};

#endif // CPROVER_GOTO_SYMEX_SIMPLIFY_EXPR_WITH_VALUE_SET_H

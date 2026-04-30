/*******************************************************************\

Module: Theory of Arrays with Extensionality

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Theory of Arrays with Extensionality

#ifndef CPROVER_SOLVERS_FLATTENING_ARRAYS_H
#define CPROVER_SOLVERS_FLATTENING_ARRAYS_H

#include "maps.h"

class array_comprehension_exprt;
class array_exprt;
class array_of_exprt;
class equal_exprt;
class if_exprt;
class symbol_exprt;
class with_exprt;
class update_exprt;

class arrayst : public mapst
{
public:
  arrayst(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &message_handler,
    bool get_constraints = false);

  // NOLINTNEXTLINE(readability/identifiers)
  typedef mapst SUB;

  literalt record_equality(const equal_exprt &expr) override;

  /// Record that \p symbol is equal to \p value for the purposes of the
  /// array theory. For unbounded-array-typed bindings this connects the
  /// two expressions in the union-find so that element-wise constraints
  /// propagate correctly.
  /// \pre \p value must be free of byte_update operators; lower them at the
  ///   call site (collect_arrays otherwise fails a DATA_INVARIANT).
  void
  record_let_binding(const symbol_exprt &symbol, const exprt &value) override;

protected:
  message_handlert &message_handler;

  void finish_eager_conversion_maps() override
  {
    add_array_constraints();
  }

  void add_array_constraints();
  void add_array_constraints(const key_sett &key_set, const exprt &expr);
  void add_array_constraints_if(const key_sett &key_set, const if_exprt &exprt);
  void
  add_array_constraints_with(const key_sett &key_set, const with_exprt &expr);
  void add_array_constraints_update(
    const key_sett &key_set,
    const update_exprt &expr);
  void add_array_constraints_array_of(
    const key_sett &key_set,
    const array_of_exprt &exprt);
  void add_array_constraints_array_constant(
    const key_sett &key_set,
    const array_exprt &exprt);
  void add_array_constraints_comprehension(
    const key_sett &key_set,
    const array_comprehension_exprt &expr);
};

#endif // CPROVER_SOLVERS_FLATTENING_ARRAYS_H

/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones owen.jones@diffblue.com

\*******************************************************************/

/// \file
/// Tracks the user-supplied configuration for VSD and build the
/// correct type of abstract object when needed.  Note this is a factory
/// within the domain and so is lower-level than the abstract domain
/// factory that is part of the ai_baset interface.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/data_dependency_context.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/monotonic_change.h>
#include <analyses/variable-sensitivity/two_value_array_abstract_object.h>
#include <analyses/variable-sensitivity/two_value_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/two_value_struct_abstract_object.h>
#include <analyses/variable-sensitivity/two_value_union_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_configuration.h>
#include <analyses/variable-sensitivity/write_location_context.h>

#include "abstract_object.h"

class variable_sensitivity_object_factoryt;
using variable_sensitivity_object_factory_ptrt =
  std::shared_ptr<variable_sensitivity_object_factoryt>;

class variable_sensitivity_object_factoryt
{
public:
  static variable_sensitivity_object_factory_ptrt
  configured_with(const vsd_configt &options)
  {
    return std::make_shared<variable_sensitivity_object_factoryt>(options);
  }

  explicit variable_sensitivity_object_factoryt(const vsd_configt &options)
    : configuration{options}, heap_allocations(0)
  {
  }

  // Return whether the current configuration is for the abstract interpretation
  // of monotonic change (i.e. MONOTONIC_CHANGE). This information is necessry
  // when we want to use a function designated to MONOTONIC_CHANGE.
  bool is_predicate_abstraction(const typet &type, const namespacet &ns) const;

  // Get the appropriate abstract object when a variable is declared in GOTO
  // code. In most cases, we return the top. Hence, it is equivalent to
  // get_abstract_object(type, true, false, ...). However, in the case of
  // MONOTONIC_CHANGE, we return the abstrtact value "unchanged," which is
  // not the top.
  abstract_object_pointert get_abstract_object_declaration(
    const typet &type,
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  // Get an appropriate abstract object for an assginment where we do not care
  // about the right-hand side. This function is used, for example, when the
  // right-hand side is a symbol/variable (e.g. x := y) or a constant (x := 42).
  // If the right-hand side is a more complicated expression (e.g. arithmetic
  // expressions), then we will examine the right-hand side more closely. For
  // instance, if the assignment is x := x + 1, we will not invoke this
  // function, but a different one.
  //
  // In most cases (apart from MONOTONIC_CHANGE), this function is equivalent to
  // get_abstract_object(type, true, false, ...). However, MONOTONIC_CHANGE
  // may need to be treated differently. In the current implementation of
  // monotonic-change abstract interpretation, this function simply returns the
  // top element. Hence, we can safely replace this function with
  // get_abstract_object(type, true, false, ...). However, in the future, the
  // monotonic-change abstract interpretation may be extended. For instance, we
  // may extend the abstract domain of MONOTONIC_CHANGE with one more abstract
  // value: "declared but uninitialized." This abstract value differs from
  // "unchanged" as follows. The former indicates that the variable has been
  // declared but has not been initialized to any value "explicitly" (i.e. by an
  // ASSIGN instruction). On the other hand, the latter indicates that the
  // variable has been declared and initialized (implicitly and
  // non-deterministically), but has not been initialized "explicitly" by a
  // programmer. In such an extension of the abstract interpretation, an arbitrary
  // assignment may result in different abstract values, depending on the
  // current abstract value of the variable.
  abstract_object_pointert get_abstract_object_arbitrary_assignment(
    const abstract_object_pointert &lhs_abstract_object,
    const typet &type,
    const exprt &rhs,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  /// Get the appropriate abstract object for the variable under
  /// consideration.
  ///
  /// \param type: the type of the variable
  /// \param top: whether the abstract object should be top in the
  ///             two-value domain
  /// \param bottom: whether the abstract object should be bottom in the
  ///                two-value domain
  /// \param e: if top and bottom are false this expression is used as the
  ///           starting pointer for the abstract object
  /// \param environment: the current abstract environment
  /// \param ns: namespace, used when following the input type
  ///
  /// \return An abstract object of the appropriate type.
  abstract_object_pointert get_abstract_object(
    const typet &type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  abstract_object_pointert
  wrap_with_context(const abstract_object_pointert &abstract_object) const;

  variable_sensitivity_object_factoryt() = delete;
  variable_sensitivity_object_factoryt(
    const variable_sensitivity_object_factoryt &) = delete;

  const vsd_configt &config() const
  {
    return configuration;
  }

private:
  /// Decide which abstract object type to use for the variable in question.
  ///
  /// \param type: the type of the variable the abstract object is
  ///              meant to represent
  ///
  /// \return An enum indicating the abstract object type to use.
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(const typet &type) const;

  vsd_configt configuration;
  mutable size_t heap_allocations;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H // NOLINT(*)

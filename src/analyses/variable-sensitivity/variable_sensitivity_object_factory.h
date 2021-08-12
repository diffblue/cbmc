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

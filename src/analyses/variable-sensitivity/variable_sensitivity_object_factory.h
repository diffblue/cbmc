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

#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/data_dependency_context.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/pointer_abstract_object.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/union_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/write_location_context.h>
#include <util/namespace.h>
#include <util/options.h>

enum ABSTRACT_OBJECT_TYPET
{
  TWO_VALUE,
  CONSTANT,
  INTERVAL,
  ARRAY_SENSITIVE,
  ARRAY_INSENSITIVE,
  POINTER_SENSITIVE,
  POINTER_INSENSITIVE,
  STRUCT_SENSITIVE,
  STRUCT_INSENSITIVE,
  // TODO: plug in UNION_SENSITIVE HERE
  UNION_INSENSITIVE,
  VALUE_SET
};

struct vsd_configt
{
  ABSTRACT_OBJECT_TYPET value_abstract_type;
  ABSTRACT_OBJECT_TYPET pointer_abstract_type;
  ABSTRACT_OBJECT_TYPET struct_abstract_type;
  ABSTRACT_OBJECT_TYPET array_abstract_type;
  ABSTRACT_OBJECT_TYPET union_abstract_type;

  struct
  {
    bool data_dependency_context;
    bool last_write_context;
  } context_tracking;

  struct
  {
    bool new_value_set;
  } advanced_sensitivities;

  static vsd_configt from_options(const optionst &options);

  static vsd_configt constant_domain();
  static vsd_configt value_set();
  static vsd_configt intervals();

  vsd_configt()
    : value_abstract_type{CONSTANT},
      pointer_abstract_type{POINTER_INSENSITIVE},
      struct_abstract_type{STRUCT_INSENSITIVE},
      array_abstract_type{ARRAY_INSENSITIVE},
      union_abstract_type{UNION_INSENSITIVE},
      context_tracking{false, true},
      advanced_sensitivities{false}
  {
  }

private:
  using option_mappingt = std::map<std::string, ABSTRACT_OBJECT_TYPET>;

  static ABSTRACT_OBJECT_TYPET option_to_abstract_type(
    const optionst &options,
    const std::string &option_name,
    const option_mappingt &mapping,
    ABSTRACT_OBJECT_TYPET default_type);

  static invalid_command_line_argument_exceptiont invalid_argument(
    const std::string &option_name,
    const std::string &bad_argument,
    const option_mappingt &mapping);

  static const option_mappingt value_option_mappings;
  static const option_mappingt pointer_option_mappings;
  static const option_mappingt struct_option_mappings;
  static const option_mappingt array_option_mappings;
  static const option_mappingt union_option_mappings;
};

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
    : configuration{options}
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

  variable_sensitivity_object_factoryt() = delete;
  variable_sensitivity_object_factoryt(
    const variable_sensitivity_object_factoryt &) = delete;

private:
  /// Decide which abstract object type to use for the variable in question.
  ///
  /// \param type: the type of the variable the abstract object is
  ///              meant to represent
  ///
  /// \return An enum indicating the abstract object type to use.
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(const typet &type) const;

  vsd_configt configuration;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H // NOLINT(*)

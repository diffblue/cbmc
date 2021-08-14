/*******************************************************************\

 Module: variable sensitivity configuration

 Author: Jez Higgins

\*******************************************************************/
/// \file
/// Captures the user-supplied configuration for VSD, determining which
/// domain abstractions are used, flow sensitivity, etc
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_CONFIGURATION_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_CONFIGURATION_H

#include <map>

#include <util/exception_utils.h>

class optionst;

enum ABSTRACT_OBJECT_TYPET
{
  TWO_VALUE,
  CONSTANT,
  INTERVAL,
  ARRAY_SENSITIVE,
  ARRAY_INSENSITIVE,
  VALUE_SET_OF_POINTERS,
  POINTER_SENSITIVE,
  POINTER_INSENSITIVE,
  STRUCT_SENSITIVE,
  STRUCT_INSENSITIVE,
  // TODO: plug in UNION_SENSITIVE HERE
  UNION_INSENSITIVE,
  VALUE_SET,
  HEAP_ALLOCATION
};

enum class flow_sensitivityt
{
  sensitive,
  insensitive
};

struct vsd_configt
{
  ABSTRACT_OBJECT_TYPET value_abstract_type;
  ABSTRACT_OBJECT_TYPET pointer_abstract_type;
  ABSTRACT_OBJECT_TYPET struct_abstract_type;
  ABSTRACT_OBJECT_TYPET array_abstract_type;
  ABSTRACT_OBJECT_TYPET union_abstract_type;

  flow_sensitivityt flow_sensitivity;

  size_t maximum_array_index = 0;

  struct
  {
    bool liveness;
    bool data_dependency_context;
    bool last_write_context;
  } context_tracking;

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
      flow_sensitivity{flow_sensitivityt::sensitive},
      context_tracking{false, true}
  {
  }

private:
  using option_mappingt = std::map<std::string, ABSTRACT_OBJECT_TYPET>;
  using option_size_mappingt = std::map<std::string, size_t>;

  static ABSTRACT_OBJECT_TYPET option_to_abstract_type(
    const optionst &options,
    const std::string &option_name,
    const option_mappingt &mapping,
    ABSTRACT_OBJECT_TYPET default_type);

  static size_t configure_max_array_size(const optionst &options);

  static size_t option_to_size(
    const optionst &options,
    const std::string &option_name,
    const option_size_mappingt &mapping);

  static const option_mappingt value_option_mappings;
  static const option_mappingt pointer_option_mappings;
  static const option_mappingt struct_option_mappings;
  static const option_mappingt array_option_mappings;
  static const option_size_mappingt array_option_size_mappings;
  static const option_mappingt union_option_mappings;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_CONFIGURATION_H // NOLINT(*)

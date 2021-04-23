/*******************************************************************\

 Module: variable sensitivity domain configuration

 Author: Jez Higgins

\*******************************************************************/
/// \file
/// Captures the user-supplied configuration for VSD, determining which
/// domain abstractions are used, flow sensitivity, etc
#include "variable_sensitivity_configuration.h"

#include <util/options.h>

vsd_configt vsd_configt::from_options(const optionst &options)
{
  vsd_configt config{};

  config.value_abstract_type =
    option_to_abstract_type(options, "values", value_option_mappings, CONSTANT);

  config.pointer_abstract_type = option_to_abstract_type(
    options, "pointers", pointer_option_mappings, POINTER_INSENSITIVE);

  config.struct_abstract_type = option_to_abstract_type(
    options, "structs", struct_option_mappings, STRUCT_INSENSITIVE);

  config.array_abstract_type = option_to_abstract_type(
    options, "arrays", array_option_mappings, ARRAY_INSENSITIVE);

  config.union_abstract_type = option_to_abstract_type(
    options, "unions", union_option_mappings, UNION_INSENSITIVE);

  // This should always be on (for efficiency with 3-way merge)
  config.context_tracking.last_write_context = true;
  config.context_tracking.data_dependency_context =
    options.get_bool_option("data-dependencies");

  config.flow_sensitivity = (options.get_bool_option("flow-insensitive"))
                              ? flow_sensitivityt::insensitive
                              : flow_sensitivityt::sensitive;

  return config;
}

vsd_configt vsd_configt::constant_domain()
{
  vsd_configt config{};
  config.context_tracking.last_write_context = true;
  config.value_abstract_type = CONSTANT;
  config.pointer_abstract_type = POINTER_SENSITIVE;
  config.struct_abstract_type = STRUCT_SENSITIVE;
  config.array_abstract_type = ARRAY_SENSITIVE;
  return config;
}

vsd_configt vsd_configt::value_set()
{
  vsd_configt config{};
  config.value_abstract_type = VALUE_SET;
  config.pointer_abstract_type = VALUE_SET_OF_POINTERS;
  config.struct_abstract_type = STRUCT_SENSITIVE;
  config.array_abstract_type = ARRAY_SENSITIVE;
  return config;
}

vsd_configt vsd_configt::intervals()
{
  vsd_configt config{};
  config.context_tracking.last_write_context = true;
  config.value_abstract_type = INTERVAL;
  config.pointer_abstract_type = POINTER_SENSITIVE;
  config.struct_abstract_type = STRUCT_SENSITIVE;
  config.array_abstract_type = ARRAY_SENSITIVE;
  return config;
}

const vsd_configt::option_mappingt vsd_configt::value_option_mappings = {
  {"intervals", INTERVAL},
  {"constants", CONSTANT},
  {"set-of-constants", VALUE_SET}};

const vsd_configt::option_mappingt vsd_configt::pointer_option_mappings = {
  {"top-bottom", POINTER_INSENSITIVE},
  {"constants", POINTER_SENSITIVE},
  {"value-set", VALUE_SET_OF_POINTERS}};

const vsd_configt::option_mappingt vsd_configt::struct_option_mappings = {
  {"top-bottom", STRUCT_INSENSITIVE},
  {"every-field", STRUCT_SENSITIVE}};

const vsd_configt::option_mappingt vsd_configt::array_option_mappings = {
  {"top-bottom", ARRAY_INSENSITIVE},
  {"every-element", ARRAY_SENSITIVE}};

const vsd_configt::option_mappingt vsd_configt::union_option_mappings = {
  {"top-bottom", UNION_INSENSITIVE}};

invalid_command_line_argument_exceptiont vsd_configt::invalid_argument(
  const std::string &option_name,
  const std::string &bad_argument,
  const option_mappingt &mapping)
{
  auto option = "--vsd-" + option_name;
  auto choices = std::string("");
  for(auto &kv : mapping)
  {
    choices += (!choices.empty() ? "|" : "");
    choices += kv.first;
  }

  return invalid_command_line_argument_exceptiont{
    "Unknown argument '" + bad_argument + "'", option, option + " " + choices};
}

ABSTRACT_OBJECT_TYPET vsd_configt::option_to_abstract_type(
  const optionst &options,
  const std::string &option_name,
  const option_mappingt &mapping,
  ABSTRACT_OBJECT_TYPET default_type)
{
  const auto argument = options.get_option(option_name);

  if(argument.empty())
    return default_type;

  auto selected = mapping.find(argument);
  if(selected == mapping.end())
  {
    throw invalid_argument(option_name, argument, mapping);
  }
  return selected->second;
}

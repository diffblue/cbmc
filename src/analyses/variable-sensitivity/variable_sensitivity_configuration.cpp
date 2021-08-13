/*******************************************************************\

 Module: variable sensitivity domain configuration

 Author: Jez Higgins

\*******************************************************************/
/// \file
/// Captures the user-supplied configuration for VSD, determining which
/// domain abstractions are used, flow sensitivity, etc
#include "variable_sensitivity_configuration.h"

#include <limits>
#include <util/options.h>

static void check_one_of_options(
  const optionst &options,
  const std::vector<std::string> &names);

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
  config.context_tracking.liveness = options.get_bool_option("liveness");
  check_one_of_options(options, {"data-dependencies", "liveness"});

  config.flow_sensitivity = (options.get_bool_option("flow-insensitive"))
                              ? flow_sensitivityt::insensitive
                              : flow_sensitivityt::sensitive;

  config.maximum_array_index = configure_max_array_size(options);

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
  config.maximum_array_index = std::numeric_limits<size_t>::max();
  return config;
}

vsd_configt vsd_configt::value_set()
{
  vsd_configt config{};
  config.value_abstract_type = VALUE_SET;
  config.pointer_abstract_type = VALUE_SET_OF_POINTERS;
  config.struct_abstract_type = STRUCT_SENSITIVE;
  config.array_abstract_type = ARRAY_SENSITIVE;
  config.maximum_array_index = std::numeric_limits<size_t>::max();
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
  config.maximum_array_index = std::numeric_limits<size_t>::max();
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
  {"smash", ARRAY_SENSITIVE},
  {"up-to-n-elements", ARRAY_SENSITIVE},
  {"every-element", ARRAY_SENSITIVE}};

const vsd_configt::option_size_mappingt
  vsd_configt::array_option_size_mappings = {
    {"top-bottom", 0},
    {"smash", 0},
    {"up-to-n-elements", 10},
    {"every-element", std::numeric_limits<size_t>::max()}};

const vsd_configt::option_mappingt vsd_configt::union_option_mappings = {
  {"top-bottom", UNION_INSENSITIVE}};

template <class mappingt>
invalid_command_line_argument_exceptiont invalid_argument(
  const std::string &option_name,
  const std::string &bad_argument,
  const mappingt &mapping)
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

size_t vsd_configt::configure_max_array_size(const optionst &options)
{
  if(options.get_option("arrays") == "up-to-n-elements")
  {
    size_t max_elements = options.get_unsigned_int_option("array-max-elements");
    if(max_elements != 0)
      return max_elements - 1;
  }
  return option_to_size(options, "arrays", array_option_size_mappings);
}

size_t vsd_configt::option_to_size(
  const optionst &options,
  const std::string &option_name,
  const option_size_mappingt &mapping)
{
  const size_t def = std::numeric_limits<size_t>::max();
  const auto argument = options.get_option(option_name);

  if(argument.empty())
    return def;

  auto selected = mapping.find(argument);
  if(selected == mapping.end())
  {
    throw invalid_argument(option_name, argument, mapping);
  }
  return selected->second;
}

void check_one_of_options(
  const optionst &options,
  const std::vector<std::string> &names)
{
  int how_many = 0;
  for(auto &name : names)
    how_many += options.get_bool_option(name);

  if(how_many <= 1)
    return;

  auto choices = std::string("");
  for(auto &name : names)
  {
    choices += (!choices.empty() ? "|" : "");
    auto option = "--vsd-" + name;
    choices += option;
  }

  throw invalid_command_line_argument_exceptiont{"Conflicting arguments",
                                                 "Can only use of " + choices};
}

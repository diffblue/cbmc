/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/
#include "variable_sensitivity_object_factory.h"
#include "interval_array_abstract_object.h"
#include "util/namespace.h"
#include "value_set_abstract_value.h"

const vsd_configt::option_mappingt vsd_configt::value_option_mappings = {
  { "intervals", INTERVAL },
  { "constants", CONSTANT },
  { "set-of-constants", VALUE_SET }
};

const vsd_configt::option_mappingt vsd_configt::pointer_option_mappings = {
  { "top-bottom", POINTER_INSENSITIVE },
  { "constants", POINTER_SENSITIVE },
  { "value-set", VALUE_SET }
};

const vsd_configt::option_mappingt vsd_configt::struct_option_mappings = {
  { "top-bottom", STRUCT_INSENSITIVE },
  { "every-field", STRUCT_SENSITIVE }
};

const vsd_configt::option_mappingt vsd_configt::array_option_mappings = {
  { "top-bottom", ARRAY_INSENSITIVE },
  { "every-element", ARRAY_SENSITIVE }
};

invalid_command_line_argument_exceptiont vsd_configt::invalid_argument(
  const std::string& option_name,
  const std::string& bad_argument,
  const option_mappingt& mapping
) {
  auto option = "--vsd-" + option_name;
  auto choices = std::string("");
  for (auto& kv : mapping) {
    choices += (!choices.empty() ? "|" : "");
    choices += kv.first;
  }

  return invalid_command_line_argument_exceptiont {
    "Unknown argument '" + bad_argument + "'",
    option,
    option + " " + choices };
}

ABSTRACT_OBJECT_TYPET vsd_configt::option_to_abstract_type(
  const optionst& options,
  const std::string& option_name,
  const option_mappingt& mapping,
  ABSTRACT_OBJECT_TYPET default_type
) {
  const auto argument = options.get_option(option_name);

  if (argument.empty()) return default_type;

  auto selected = mapping.find(argument);
  if (selected == mapping.end()) {
    throw invalid_argument(option_name, argument, mapping);
  }
  return selected->second;
}

ABSTRACT_OBJECT_TYPET
variable_sensitivity_object_factoryt::get_abstract_object_type(const typet type)
{
  ABSTRACT_OBJECT_TYPET abstract_object_type = TWO_VALUE;

  if(
    type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
    type.id() == ID_fixedbv || type.id() == ID_c_bool || type.id() == ID_bool ||
    type.id() == ID_integer || type.id() == ID_c_bit_field)
  {
    return configuration.value_abstract_type;
  }
  else if(type.id() == ID_floatbv)
  {
    auto float_type = configuration.value_abstract_type;
    return (float_type == INTERVAL) ? CONSTANT : float_type;
  }
  else if(type.id() == ID_array)
  {
    return configuration.array_abstract_type;
  }
  else if(type.id() == ID_pointer)
  {
    return configuration.pointer_abstract_type;
  }
  else if(type.id() == ID_struct)
  {
    return configuration.struct_abstract_type;
  }
  else if(type.id() == ID_union)
  {
    abstract_object_type = UNION_INSENSITIVE;
  }

  return abstract_object_type;
}

abstract_object_pointert
variable_sensitivity_object_factoryt::get_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(!initialized)
  {
    throw "variable_sensitivity_object_factoryt::get_abstract_object() " \
      "called without first calling " \
      "variable_sensitivity_object_factoryt::set_options()\n";
  }

  typet followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type =
    get_abstract_object_type(followed_type);

  switch(abstract_object_type)
  {
  case CONSTANT:
    return initialize_abstract_object<constant_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns);
  case INTERVAL:
    return initialize_abstract_object<interval_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns);
  case ARRAY_SENSITIVE:
    return configuration.value_abstract_type == INTERVAL
             ? initialize_abstract_object<interval_array_abstract_objectt>(
                 followed_type, top, bottom, e, environment, ns)
             : initialize_abstract_object<constant_array_abstract_objectt>(
                 followed_type, top, bottom, e, environment, ns);
  case ARRAY_INSENSITIVE:
    return initialize_abstract_object<array_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case POINTER_SENSITIVE:
    return initialize_abstract_object<constant_pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case POINTER_INSENSITIVE:
    return initialize_abstract_object<pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case STRUCT_SENSITIVE:
    return initialize_abstract_object<full_struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case STRUCT_INSENSITIVE:
    return initialize_abstract_object<struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case UNION_INSENSITIVE:
    return initialize_abstract_object<union_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case TWO_VALUE:
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  case VALUE_SET:
    if(configuration.advanced_sensitivities.new_value_set)
    {
      return initialize_abstract_object<value_set_abstract_valuet>(
        followed_type, top, bottom, e, environment, ns);
    }
    return initialize_abstract_object<value_set_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  default:
    UNREACHABLE;
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  }
}

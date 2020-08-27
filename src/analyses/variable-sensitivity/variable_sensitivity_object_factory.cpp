/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/
#include "variable_sensitivity_object_factory.h"
#include "interval_array_abstract_object.h"
#include "util/namespace.h"

variable_sensitivity_object_factoryt
  variable_sensitivity_object_factoryt::s_instance;

/// Function: variable_sensitivity_object_factoryt::get_abstract_object_type
///
/// \param type: the type of the variable the abstract object is meant to represent
///
/// \return An enum indicating the abstract object type to use.
///
/// Decide which abstract object type to use for the variable in question.
variable_sensitivity_object_factoryt::ABSTRACT_OBJECT_TYPET
variable_sensitivity_object_factoryt::get_abstract_object_type(const typet type)
{
  ABSTRACT_OBJECT_TYPET abstract_object_type = TWO_VALUE;

  if(
    type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
    type.id() == ID_fixedbv || type.id() == ID_c_bool || type.id() == ID_bool ||
    type.id() == ID_integer || type.id() == ID_c_bit_field)
  {
    abstract_object_type =
      configuration.advanced_sensitivities.intervals ? INTERVAL : CONSTANT;
  }
  else if(type.id() == ID_floatbv)
  {
    abstract_object_type = CONSTANT;
  }
  else if(type.id() == ID_array)
  {
    abstract_object_type = configuration.primitive_sensitivity.array_sensitivity
                             ? ARRAY_SENSITIVE
                             : ARRAY_INSENSITIVE;
  }
  else if(type.id() == ID_pointer)
  {
    abstract_object_type =
      configuration.primitive_sensitivity.pointer_sensitivity
        ? POINTER_SENSITIVE
        : POINTER_INSENSITIVE;
  }
  else if(type.id() == ID_struct)
  {
    abstract_object_type =
      configuration.primitive_sensitivity.struct_sensitivity
        ? STRUCT_SENSITIVE
        : STRUCT_INSENSITIVE;
  }
  else if(type.id() == ID_union)
  {
    abstract_object_type = UNION_INSENSITIVE;
  }
  if(
    configuration.advanced_sensitivities.value_set &&
    (abstract_object_type == INTERVAL || abstract_object_type == CONSTANT ||
     abstract_object_type == POINTER_INSENSITIVE ||
     abstract_object_type == POINTER_SENSITIVE))
  {
    abstract_object_type = VALUE_SET;
  }

  return abstract_object_type;
}

/// Function: variable_sensitivity_object_factoryt::get_abstract_object
///
/// \param type: the type of the variable
/// \param top: whether the abstract object should be top in the two-value domain
/// \param bottom: whether the abstract object should be bottom in the two-value domain
/// \param e: if top and bottom are false this expression is used as the starting
///           pointer for the abstract object
/// \param ns: namespace, used when following the input type
///
/// \return An abstract object of the appropriate type.
///
/// Get the appropriate abstract object for the variable under
/// consideration.
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
    return configuration.advanced_sensitivities.intervals
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
    return initialize_abstract_object<value_set_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  default:
    UNREACHABLE;
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns);
  }
}

/// Function: variable_sensitivity_object_factoryt::set_options
///
/// \param options: the command line options
///
/// Called once to record the appropriate variables from the command line
/// options so that they can be accessed easily when they are needed.
void variable_sensitivity_object_factoryt::set_options(
  const vsd_configt &options)
{
  this->configuration = options;
  initialized = true;
}

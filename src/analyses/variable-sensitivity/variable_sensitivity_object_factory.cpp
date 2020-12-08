/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/
#include "variable_sensitivity_object_factory.h"
#include "interval_array_abstract_object.h"
#include "value_set_abstract_value.h"

template <class abstract_object_classt, class context_classt>
abstract_object_pointert initialize_context_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(top || bottom)
  {
    return abstract_object_pointert(new context_classt{
      abstract_object_pointert(new abstract_object_classt{type, top, bottom}),
      type,
      top,
      bottom});
  }
  else
  {
    PRECONDITION(type == ns.follow(e.type()));
    return abstract_object_pointert(new context_classt{
      abstract_object_pointert(new abstract_object_classt{e, environment, ns}),
      e,
      environment,
      ns});
  }
}

/// Function: variable_sensitivity_object_factoryt::initialize_abstract_object
/// Initialize the abstract object class and return it.
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
///
template <class abstract_object_classt>
abstract_object_pointert initialize_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns,
  const vsd_configt &configuration)
{
  if(configuration.context_tracking.data_dependency_context)
    return initialize_context_abstract_object<
      abstract_object_classt,
      data_dependency_contextt>(type, top, bottom, e, environment, ns);
  if(configuration.context_tracking.last_write_context)
    return initialize_context_abstract_object<
      abstract_object_classt,
      write_location_contextt>(type, top, bottom, e, environment, ns);
  else
  {
    if(top || bottom)
    {
      return abstract_object_pointert(
        new abstract_object_classt{type, top, bottom});
    }
    else
    {
      PRECONDITION(type == ns.follow(e.type()));
      return abstract_object_pointert(
        new abstract_object_classt{e, environment, ns});
    }
  }
}

ABSTRACT_OBJECT_TYPET
variable_sensitivity_object_factoryt::get_abstract_object_type(
  const typet &type) const
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
    return configuration.union_abstract_type;
  }

  return abstract_object_type;
}

abstract_object_pointert
variable_sensitivity_object_factoryt::get_abstract_object(
  const typet &type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  const typet &followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type =
    get_abstract_object_type(followed_type);

  switch(abstract_object_type)
  {
  case CONSTANT:
    return initialize_abstract_object<constant_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case INTERVAL:
    return initialize_abstract_object<interval_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case ARRAY_SENSITIVE:
    return configuration.value_abstract_type == INTERVAL
             ? initialize_abstract_object<interval_array_abstract_objectt>(
                 followed_type, top, bottom, e, environment, ns, configuration)
             : initialize_abstract_object<constant_array_abstract_objectt>(
                 followed_type, top, bottom, e, environment, ns, configuration);
  case ARRAY_INSENSITIVE:
    return initialize_abstract_object<array_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case POINTER_SENSITIVE:
    return initialize_abstract_object<constant_pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case POINTER_INSENSITIVE:
    return initialize_abstract_object<pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case STRUCT_SENSITIVE:
    return initialize_abstract_object<full_struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case STRUCT_INSENSITIVE:
    return initialize_abstract_object<struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case UNION_INSENSITIVE:
    return initialize_abstract_object<union_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case TWO_VALUE:
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case VALUE_SET:
    if(configuration.advanced_sensitivities.new_value_set)
    {
      return initialize_abstract_object<value_set_abstract_valuet>(
        followed_type, top, bottom, e, environment, ns, configuration);
    }
    return initialize_abstract_object<value_set_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  default:
    UNREACHABLE;
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  }
}

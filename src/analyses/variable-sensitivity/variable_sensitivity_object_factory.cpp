/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/
#include "variable_sensitivity_object_factory.h"
#include "abstract_value_object.h"
#include "full_array_abstract_object.h"
#include "liveness_context.h"
#include "monotonic_change.h"
#include "value_set_pointer_abstract_object.h"

template <class context_classt>
abstract_object_pointert
create_context_abstract_object(const abstract_object_pointert &abstract_object)
{
  return abstract_object_pointert(
    new context_classt{abstract_object, abstract_object->type()});
}

template <class abstract_object_classt>
abstract_object_pointert create_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(top || bottom)
    return std::make_shared<abstract_object_classt>(type, top, bottom);

  PRECONDITION(type == ns.follow(e.type()));
  return std::make_shared<abstract_object_classt>(e, environment, ns);
}

abstract_object_pointert wrap_with_context_object(
  const abstract_object_pointert &abstract_object,
  const vsd_configt &configuration)
{
  if(configuration.context_tracking.liveness)
    return create_context_abstract_object<liveness_contextt>(abstract_object);

  if(configuration.context_tracking.data_dependency_context)
    return create_context_abstract_object<data_dependency_contextt>(
      abstract_object);

  if(configuration.context_tracking.last_write_context)
    return create_context_abstract_object<write_location_contextt>(
      abstract_object);

  return abstract_object;
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
/// \param configuration: variable sensitivity domain configuration
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
  auto abstract_object = create_abstract_object<abstract_object_classt>(
    type, top, bottom, e, environment, ns);

  return wrap_with_context_object(abstract_object, configuration);
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
  else if(type.id() == ID_dynamic_object)
  {
    return HEAP_ALLOCATION;
  }

  return abstract_object_type;
}

bool variable_sensitivity_object_factoryt::is_predicate_abstraction(
  const typet &type,
  const namespacet &ns) const
{
  const typet &followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type =
    get_abstract_object_type(followed_type);

  if(abstract_object_type == MONOTONIC_CHANGE)
    return true;
  else
    return false;
}

abstract_object_pointert
variable_sensitivity_object_factoryt::get_abstract_object_declaration(
  const typet &type,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  const typet &followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type =
    get_abstract_object_type(followed_type);

  bool top = true;
  bool bottom = false;

  abstract_object_pointert abstract_object;

  switch(abstract_object_type)
  {
  case TWO_VALUE:
    abstract_object =
      std::make_shared<abstract_objectt>(followed_type, top, bottom);
    break;
  case CONSTANT:
    abstract_object =
      std::make_shared<constant_abstract_valuet>(followed_type, top, bottom);
    break;
  case INTERVAL:
    abstract_object =
      std::make_shared<interval_abstract_valuet>(followed_type, top, bottom);
    break;
  case VALUE_SET:
    abstract_object =
      std::make_shared<value_set_abstract_objectt>(followed_type, top, bottom);
    break;
  case MONOTONIC_CHANGE:
    // For MONOTONIC_CHANGE, an initial abstract object is NOT the top. Instead,
    // it is the abstract value "unchanged."
    abstract_object = std::make_shared<monotonic_changet>(
      followed_type, false, false, unchanged);
    break;

  case ARRAY_INSENSITIVE:
    abstract_object = std::make_shared<two_value_array_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case ARRAY_SENSITIVE:
    abstract_object =
      std::make_shared<full_array_abstract_objectt>(followed_type, top, bottom);
    break;

  case POINTER_INSENSITIVE:
    abstract_object = std::make_shared<two_value_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case POINTER_SENSITIVE:
    abstract_object = std::make_shared<constant_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case VALUE_SET_OF_POINTERS:
    abstract_object = std::make_shared<value_set_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case STRUCT_INSENSITIVE:
    abstract_object = std::make_shared<two_value_struct_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case STRUCT_SENSITIVE:
    abstract_object = std::make_shared<full_struct_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case UNION_INSENSITIVE:
    abstract_object = std::make_shared<two_value_union_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case HEAP_ALLOCATION:
  {
    auto dynamic_object = exprt(ID_dynamic_object);
    dynamic_object.set(
      ID_identifier, "heap-allocation-" + std::to_string(heap_allocations++));
    auto heap_symbol = unary_exprt(ID_address_of, dynamic_object, e.type());
    auto heap_pointer =
      get_abstract_object(e.type(), false, false, heap_symbol, environment, ns);
    return heap_pointer;
  }

  default:
    UNREACHABLE;
    abstract_object =
      std::make_shared<abstract_objectt>(followed_type, top, bottom);
  }

  return wrap_with_context_object(abstract_object, configuration);
}

abstract_object_pointert
variable_sensitivity_object_factoryt::get_abstract_object_arbitrary_assignment(
  const abstract_object_pointert &lhs_abstract_object,
  const typet &type,
  const exprt &rhs,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  const typet &followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type =
    get_abstract_object_type(followed_type);

  bool top = false;
  bool bottom = false;

  abstract_object_pointert abstract_object;

  switch(abstract_object_type)
  {
  case TWO_VALUE:
    abstract_object =
      std::make_shared<abstract_objectt>(followed_type, top, bottom);
    break;
  case CONSTANT:
    abstract_object =
      std::make_shared<constant_abstract_valuet>(followed_type, top, bottom);
    break;
  case INTERVAL:
    abstract_object =
      std::make_shared<interval_abstract_valuet>(followed_type, top, bottom);
    break;
  case VALUE_SET:
    abstract_object =
      std::make_shared<value_set_abstract_objectt>(followed_type, top, bottom);
    break;
  case MONOTONIC_CHANGE:
    // For MONOTONIC_CHANGE, we check the left-hand side's current abstract
    // value of monotonic change.
    abstract_object = monotonic_change_expression_transform(
      lhs_abstract_object,
      // We don't care about the left-hand side's expression, so we just pass
      // nil_expret().
      nil_exprt(),
      rhs);
    break;

  case ARRAY_INSENSITIVE:
    abstract_object = std::make_shared<two_value_array_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case ARRAY_SENSITIVE:
    abstract_object =
      std::make_shared<full_array_abstract_objectt>(followed_type, top, bottom);
    break;

  case POINTER_INSENSITIVE:
    abstract_object = std::make_shared<two_value_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case POINTER_SENSITIVE:
    abstract_object = std::make_shared<constant_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case VALUE_SET_OF_POINTERS:
    abstract_object = std::make_shared<value_set_pointer_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case STRUCT_INSENSITIVE:
    abstract_object = std::make_shared<two_value_struct_abstract_objectt>(
      followed_type, top, bottom);
    break;
  case STRUCT_SENSITIVE:
    abstract_object = std::make_shared<full_struct_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case UNION_INSENSITIVE:
    abstract_object = std::make_shared<two_value_union_abstract_objectt>(
      followed_type, top, bottom);
    break;

  case HEAP_ALLOCATION:
  {
    auto dynamic_object = exprt(ID_dynamic_object);
    dynamic_object.set(
      ID_identifier, "heap-allocation-" + std::to_string(heap_allocations++));
    auto heap_symbol = unary_exprt(ID_address_of, dynamic_object, rhs.type());
    auto heap_pointer = get_abstract_object(
      rhs.type(), false, false, heap_symbol, environment, ns);
    return heap_pointer;
  }

  default:
    UNREACHABLE;
    abstract_object =
      std::make_shared<abstract_objectt>(followed_type, top, bottom);
  }

  return wrap_with_context_object(abstract_object, configuration);
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
  case TWO_VALUE:
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case CONSTANT:
    return initialize_abstract_object<constant_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case INTERVAL:
    return initialize_abstract_object<interval_abstract_valuet>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case VALUE_SET:
    return initialize_abstract_object<value_set_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case MONOTONIC_CHANGE:
    return initialize_abstract_object<monotonic_changet>(
      followed_type, top, bottom, e, environment, ns, configuration);

  case ARRAY_INSENSITIVE:
    return initialize_abstract_object<two_value_array_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case ARRAY_SENSITIVE:
    return initialize_abstract_object<full_array_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);

  case POINTER_INSENSITIVE:
    return initialize_abstract_object<two_value_pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case POINTER_SENSITIVE:
    return initialize_abstract_object<constant_pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case VALUE_SET_OF_POINTERS:
    return initialize_abstract_object<value_set_pointer_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);

  case STRUCT_INSENSITIVE:
    return initialize_abstract_object<two_value_struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  case STRUCT_SENSITIVE:
    return initialize_abstract_object<full_struct_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);

  case UNION_INSENSITIVE:
    return initialize_abstract_object<two_value_union_abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);

  case HEAP_ALLOCATION:
  {
    auto dynamic_object = exprt(ID_dynamic_object);
    dynamic_object.set(
      ID_identifier, "heap-allocation-" + std::to_string(heap_allocations++));
    auto heap_symbol = unary_exprt(ID_address_of, dynamic_object, e.type());
    auto heap_pointer =
      get_abstract_object(e.type(), false, false, heap_symbol, environment, ns);
    return heap_pointer;
  }

  default:
    UNREACHABLE;
    return initialize_abstract_object<abstract_objectt>(
      followed_type, top, bottom, e, environment, ns, configuration);
  }
}

abstract_object_pointert
variable_sensitivity_object_factoryt::wrap_with_context(
  const abstract_object_pointert &abstract_object) const
{
  return wrap_with_context_object(abstract_object, configuration);
}

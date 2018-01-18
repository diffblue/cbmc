/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/
#include "variable_sensitivity_object_factory.h"
#include "util/namespace.h"

variable_sensitivity_object_factoryt
  variable_sensitivity_object_factoryt::s_instance;

/*******************************************************************\

Function: variable_sensitivity_object_factoryt::get_abstract_object_type

 Inputs:
  type - the type of the variable the abstract object is meant to represent

 Outputs: An enum indicating the abstract object type to use.

 Purpose: Decide which abstract object type to use for the variable in question.

\*******************************************************************/

variable_sensitivity_object_factoryt::ABSTRACT_OBJECT_TYPET
  variable_sensitivity_object_factoryt::get_abstract_object_type(
  const typet type)
{
  ABSTRACT_OBJECT_TYPET abstract_object_type=TWO_VALUE;

  if(type.id()==ID_signedbv || type.id()==ID_unsignedbv ||
    type.id()==ID_floatbv || type.id()==ID_fixedbv ||
    type.id()==ID_c_bool || type.id()==ID_bool ||
    type.id()==ID_integer || type.id()==ID_c_bit_field)
  {
    abstract_object_type=CONSTANT;
  }
  else if(type.id()==ID_array)
  {
    abstract_object_type=has_arrays_flag?ARRAY_SENSITIVE:ARRAY_INSENSITIVE;
  }
  else if(type.id()==ID_pointer)
  {
    abstract_object_type=
      has_pointers_flag?POINTER_SENSITIVE:POINTER_INSENSITIVE;
  }
  else if(type.id()==ID_struct)
  {
    abstract_object_type=has_structs_flag?STRUCT_SENSITIVE:STRUCT_INSENSITIVE;
  }
  else if(type.id()==ID_union)
  {
    abstract_object_type=UNION_INSENSITIVE;
  }

  return abstract_object_type;
}

/*******************************************************************\

Function: variable_sensitivity_object_factoryt::get_abstract_object

 Inputs:
  type - the type of the variable
  top - whether the abstract object should be top in the two-value domain
  bottom - whether the abstract object should be bottom in the two-value domain
  e - if top and bottom are false this expression is used as the starting
      pointer for the abstract object
  ns - namespace, used when following the input type

 Outputs: An abstract object of the appropriate type.

 Purpose: Get the appropriate abstract object for the variable under
          consideration.

\*******************************************************************/

abstract_object_pointert variable_sensitivity_object_factoryt::
  get_abstract_object(
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

  typet followed_type=ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type=
    get_abstract_object_type(followed_type);

  switch(abstract_object_type)
  {
  case CONSTANT:
    return initialize_abstract_object<
      context_abstract_objectt<constant_abstract_valuet>>(
        followed_type, top, bottom, e, environment, ns);
  case ARRAY_SENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<constant_array_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case ARRAY_INSENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<array_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case POINTER_SENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<constant_pointer_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case POINTER_INSENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<pointer_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case STRUCT_SENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<full_struct_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case STRUCT_INSENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<struct_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case UNION_INSENSITIVE:
    return initialize_abstract_object<
      context_abstract_objectt<union_abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  case TWO_VALUE:
    return initialize_abstract_object<
      context_abstract_objectt<abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  default:
    UNREACHABLE;
    return initialize_abstract_object<
      context_abstract_objectt<abstract_objectt>>(
        followed_type, top, bottom, e, environment, ns);
  }
}

/*******************************************************************\

Function: variable_sensitivity_object_factoryt::set_options

 Inputs:
  options - the command line options

 Outputs:

 Purpose: Called once to record the appropriate variables from the command line
          options so that they can be accessed easily when they are needed.

\*******************************************************************/

void variable_sensitivity_object_factoryt::set_options(const optionst &options)
{
  has_variables_flag=options.get_bool_option("variable");
  has_structs_flag=options.get_bool_option("structs");
  has_arrays_flag=options.get_bool_option("arrays");
  has_pointers_flag=options.get_bool_option("pointers");
  initialized=true;
}

/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones owen.jones@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/pointer_abstract_object.h>
#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/union_abstract_object.h>
#include <analyses/variable-sensitivity/dependency_context_abstract_object.h>
#include <util/options.h>
#include <util/namespace.h>


class variable_sensitivity_object_factoryt
{
public:
  static variable_sensitivity_object_factoryt &instance()
  {
    return s_instance;
  }
  abstract_object_pointert get_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);
  void set_options(const optionst &options);

private:
  variable_sensitivity_object_factoryt():initialized(false)
  {}
  static variable_sensitivity_object_factoryt s_instance;
  enum ABSTRACT_OBJECT_TYPET
  {
    TWO_VALUE,
    CONSTANT,
    ARRAY_SENSITIVE,
    ARRAY_INSENSITIVE,
    POINTER_SENSITIVE,
    POINTER_INSENSITIVE,
    STRUCT_SENSITIVE,
    STRUCT_INSENSITIVE,
    // TODO: plug in UNION_SENSITIVE HERE
    UNION_INSENSITIVE
  };
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(const typet type);
  template <class abstract_object_class>
  abstract_object_pointert initialize_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
  bool has_variables_flag;
  bool has_structs_flag;
  bool has_arrays_flag;
  bool has_pointers_flag;
  bool initialized;
};

/*******************************************************************\

Function: variable_sensitivity_object_factoryt::initialize_abstract_object

 Inputs:
  abstract_object_classt - the class to use for the abstract object
  type - the type of the variable
  top - whether the abstract object should be top in the two-value domain
  bottom - whether the abstract object should be bottom in the two-value domain
  e - if top and bottom are false this expression is used as the starting
      pointer for the abstract object
  ns - namespace, used when following the input type

 Outputs: An abstract object of the appropriate type.

 Purpose: Initialize the abstract object class and return it.

\*******************************************************************/

template <class abstract_object_classt>
abstract_object_pointert variable_sensitivity_object_factoryt::
  initialize_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns)
{
  if(top || bottom)
  {
    return abstract_object_pointert(
      new abstract_object_classt(type, top, bottom));
  }
  else
  {
    assert(type==ns.follow(e.type()));
    return abstract_object_pointert(
      new abstract_object_classt(e, enviroment, ns));
  }
}

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H // NOLINT(*)

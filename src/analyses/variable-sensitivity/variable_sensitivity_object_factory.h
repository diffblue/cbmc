/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones owen.jones@diffblue.com

\*******************************************************************/
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

struct vsd_configt
{
  struct
  {
    bool struct_sensitivity;
    bool array_sensitivity;
    bool pointer_sensitivity;
  } primitive_sensitivity;

  struct
  {
    bool data_dependency_context;
    bool last_write_context;
  } context_tracking;

  struct
  {
    bool intervals;
    bool value_set;
  } advanced_sensitivities;

  static vsd_configt from_options(const optionst &options)
  {
    vsd_configt config{};

    if(
      options.get_bool_option("value-set") &&
      options.get_bool_option("data-dependencies"))
    {
      throw invalid_command_line_argument_exceptiont{
        "Value set is not currently supported with data dependency analysis",
        "--value-set --data-dependencies",
        "--data-dependencies"};
    }

    config.primitive_sensitivity.struct_sensitivity =
      options.get_bool_option("structs");
    config.primitive_sensitivity.array_sensitivity =
      options.get_bool_option("arrays");
    config.primitive_sensitivity.pointer_sensitivity =
      options.get_bool_option("pointers");

    // This should always be on (for efficeny with 3-way merge)
    // Does not work with value set
    config.context_tracking.last_write_context =
      !options.get_bool_option("value-set");
    config.context_tracking.data_dependency_context =
      options.get_bool_option("data-dependencies");
    config.advanced_sensitivities.intervals =
      options.get_bool_option("interval");
    config.advanced_sensitivities.value_set =
      options.get_bool_option("value-set");

    return config;
  }

  static vsd_configt constant_domain()
  {
    vsd_configt config{};
    config.primitive_sensitivity.pointer_sensitivity = true;
    config.primitive_sensitivity.array_sensitivity = true;
    config.primitive_sensitivity.struct_sensitivity = true;
    config.context_tracking.last_write_context = true;
    return config;
  }

  static vsd_configt value_set()
  {
    vsd_configt config{};
    config.primitive_sensitivity.pointer_sensitivity = true;
    config.primitive_sensitivity.array_sensitivity = true;
    config.primitive_sensitivity.struct_sensitivity = true;
    config.advanced_sensitivities.value_set = true;
    return config;
  }

  static vsd_configt intervals()
  {
    vsd_configt config{};
    config.primitive_sensitivity.pointer_sensitivity = true;
    config.primitive_sensitivity.array_sensitivity = true;
    config.primitive_sensitivity.struct_sensitivity = true;
    config.context_tracking.last_write_context = true;
    config.advanced_sensitivities.intervals = true;
    return config;
  }
};

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
  void set_options(const vsd_configt &options);

private:
  variable_sensitivity_object_factoryt():initialized(false)
  {}
  static variable_sensitivity_object_factoryt s_instance;
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
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(const typet type);
  template <class abstract_object_class>
  abstract_object_pointert initialize_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
  template <class abstract_object_class, class context_classt>
  abstract_object_pointert initialize_context_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
  vsd_configt configuration;
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
  if(configuration.context_tracking.data_dependency_context)
    return initialize_context_abstract_object<
      abstract_object_classt, data_dependency_contextt>(
        type, top, bottom, e, enviroment, ns);
  if(configuration.context_tracking.last_write_context)
    return initialize_context_abstract_object<
      abstract_object_classt, write_location_contextt>(
        type, top, bottom, e, enviroment, ns);
  else
  {
    if(top || bottom)
    {
      return abstract_object_pointert(
        new abstract_object_classt(type, top, bottom));
    }
    else
    {
      PRECONDITION(type == ns.follow(e.type()));
      return abstract_object_pointert(
        new abstract_object_classt(e, enviroment, ns));
    }
  }
}

template <class abstract_object_classt, class context_classt>
abstract_object_pointert variable_sensitivity_object_factoryt::
  initialize_context_abstract_object(
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
      new context_classt(
        abstract_object_pointert(
          new abstract_object_classt(type, top, bottom)),
        type, top, bottom));
  }
  else
  {
    PRECONDITION(type==ns.follow(e.type()));
    return abstract_object_pointert(
      new context_classt(
        abstract_object_pointert(
          new abstract_object_classt(e, enviroment, ns)),
        e, enviroment, ns));
  }
}

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H // NOLINT(*)

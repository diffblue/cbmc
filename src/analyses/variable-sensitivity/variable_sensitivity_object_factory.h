#ifndef VARIABLE_SENSITIVITY_OBJECT_FACTORY_H
#define VARIABLE_SENSITIVITY_OBJECT_FACTORY_H

#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/pointer_abstract_object.h>
#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <util/options.h>


class variable_sensitivity_object_factoryt
{
public:
  static variable_sensitivity_object_factoryt &instance()
  {
    return s_instance;
  }
  abstract_object_pointert get_abstract_object(
    const typet type, bool top, bool bottom, const exprt &e,
    const namespacet &ns);
  void set_options(optionst &options);

private:
  variable_sensitivity_object_factoryt()
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
    STRUCT_INSENSITIVE
  };
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(
    const typet type, const namespacet &ns);
  bool has_variables_flag;
  bool has_structs_flag;
  bool has_arrays_flag;
  bool has_pointers_flag;
};

#endif // VARIABLE_SENSITIVITY_OBJECT_FACTORY_H

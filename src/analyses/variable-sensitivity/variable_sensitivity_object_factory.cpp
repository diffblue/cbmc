#include "variable_sensitivity_object_factory.h"
#include "util/namespace.h"

variable_sensitivity_object_factoryt
  variable_sensitivity_object_factoryt::s_instance;

variable_sensitivity_object_factoryt::ABSTRACT_OBJECT_TYPET
  variable_sensitivity_object_factoryt::get_abstract_object_type(
  const typet type, const namespacet &ns)
{
  ABSTRACT_OBJECT_TYPET abstract_object_type=TWO_VALUE;

  if(type.id()==ID_signedbv || type.id()==ID_unsignedbv ||
    type.id()==ID_floatbv || type.id()==ID_fixedbv ||
    type.id()==ID_c_bool)
  {
    abstract_object_type=CONSTANT;
  }
  else if(type.id()==ID_array)
  {
    if(has_arrays_flag)
    {
      abstract_object_type=ARRAY_SENSITIVE;
    }
    else
    {
      abstract_object_type=ARRAY_INSENSITIVE;
    }
  }
  else if(type.id()==ID_pointer)
  {
    if(has_pointers_flag)
    {
      abstract_object_type=POINTER_SENSITIVE;
    }
    else
    {
      abstract_object_type=POINTER_INSENSITIVE;
    }
  }
  else if(type.id()==ID_struct)
  {
    if(has_structs_flag)
    {
      abstract_object_type=STRUCT_SENSITIVE;
    }
    else
    {
      abstract_object_type=STRUCT_INSENSITIVE;
    }
  }

  // TODO: deal with unions
  return abstract_object_type;
}


abstract_object_pointert variable_sensitivity_object_factoryt::
  get_abstract_object(
    const typet type, bool top, bool bottom, const exprt &e,
    const namespacet &ns)
{
  typet followed_type = ns.follow(type);
  ABSTRACT_OBJECT_TYPET abstract_object_type=get_abstract_object_type(followed_type, ns);

  if(top || bottom)
  {
    switch(abstract_object_type)
    {
      case CONSTANT:
        return abstract_object_pointert(
          new constant_abstract_valuet(followed_type, top, bottom));
      case ARRAY_SENSITIVE:
        return abstract_object_pointert(
        new array_abstract_objectt(followed_type, top, false));
      case ARRAY_INSENSITIVE:
        return abstract_object_pointert(
          new array_abstract_objectt(followed_type, top, false));
      case POINTER_SENSITIVE:
        return abstract_object_pointert(
        new constant_pointer_abstract_objectt(followed_type, top, false));
      case POINTER_INSENSITIVE:
        return abstract_object_pointert(
          new pointer_abstract_objectt(followed_type, top, false));
      case STRUCT_SENSITIVE:
        return abstract_object_pointert(
        new struct_abstract_objectt(followed_type, top, false));
      case STRUCT_INSENSITIVE:
        return abstract_object_pointert(
          new struct_abstract_objectt(followed_type, top, false));
      case TWO_VALUE:
        return abstract_object_pointert(new abstract_objectt(followed_type, top, false));
      default:
        assert(false);
        return abstract_object_pointert(new abstract_objectt(followed_type, top, false));
    }
  }
  else
  {
    assert(followed_type==e.type());
    switch(abstract_object_type)
    {
      case CONSTANT:
        return abstract_object_pointert(new constant_abstract_valuet(e));
      case ARRAY_SENSITIVE:
        return abstract_object_pointert(new array_abstract_objectt(e));
      case ARRAY_INSENSITIVE:
        return abstract_object_pointert(new array_abstract_objectt(e));
      case POINTER_SENSITIVE:
        return abstract_object_pointert(
          new constant_pointer_abstract_objectt(e));
      case POINTER_INSENSITIVE:
        return abstract_object_pointert(new pointer_abstract_objectt(e));
      case STRUCT_SENSITIVE:
        return abstract_object_pointert(new struct_abstract_objectt(e));
      case STRUCT_INSENSITIVE:
        return abstract_object_pointert(new struct_abstract_objectt(e));
      case TWO_VALUE:
        return abstract_object_pointert(new abstract_objectt(e));
      default:
        assert(false);
        return abstract_object_pointert(new abstract_objectt(e));
    }
  }
}

void variable_sensitivity_object_factoryt::set_options(optionst &options)
{
  has_variables_flag=options.get_bool_option("variable");
  has_structs_flag=options.get_bool_option("structs");
  has_arrays_flag=options.get_bool_option("arrays");
  has_pointers_flag=options.get_bool_option("pointers");
}

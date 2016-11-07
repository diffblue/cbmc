/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_TYPES_H
#define CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

#include <util/invariant.h>
#include <util/type.h>
#include <util/std_types.h>
#include <util/c_types.h>
#include <util/config.h>

class java_class_typet:public class_typet
{
 public:
  const irep_idt &get_access() const
  {
    return get(ID_access);
  }

  void set_access(const irep_idt &access)
  {
    return set(ID_access, access);
  }
};

inline const java_class_typet &to_java_class_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const java_class_typet &>(type);
}

inline java_class_typet &to_java_class_type(typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<java_class_typet &>(type);
}

typet java_int_type();
typet java_long_type();
typet java_short_type();
typet java_byte_type();
typet java_char_type();
typet java_float_type();
typet java_double_type();
typet java_boolean_type();
reference_typet java_reference_type(const typet &subtype);
reference_typet java_lang_object_type();
symbol_typet java_classname(const std::string &);

reference_typet java_array_type(const char subtype);

bool is_reference_type(char t);

// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

typet java_type_from_char(char t);
typet java_type_from_string(
  const std::string &,
  const std::string &class_name="");
char java_char_from_type(const typet &type);
std::vector<typet> java_generic_type_from_string(
  const std::string &,
  const std::string &);

typet java_bytecode_promotion(const typet &);
exprt java_bytecode_promotion(const exprt &);

bool is_java_array_tag(const irep_idt& tag);

bool is_valid_java_array(const struct_typet &type);


/// class to hold a Java generic type
/// upper bound can specify type requirements
class java_generic_parametert:public reference_typet
{
public:
  typedef symbol_typet type_variablet;
  typedef std::vector<type_variablet> type_variablest;

  java_generic_parametert(const irep_idt &_type_var_name, const typet &_bound) :
    // the reference_typet now needs a pointer width, here it uses the one
    // defined in the reference_type function from c_types.cpp
    reference_typet(_bound, config.ansi_c.pointer_width)
  {
    PRECONDITION(_bound.id()==ID_symbol);
    set(ID_C_java_generic_parameter, true);
    // bound must be symbol type
    type_variables().push_back(symbol_typet(_type_var_name));
  }

  /// \return the type variable as symbol type
  const type_variablet &type_variable() const
  {
    PRECONDITION(!type_variables().empty());
    return type_variables().front();
  }

  const type_variablest &type_variables() const
  {
    return (const type_variablest &)(find(ID_type_variables).get_sub());
  }

  type_variablest &type_variables()
  {
    return (type_variablest &)(add(ID_type_variables).get_sub());
  }
};

/// \param type: type the type to check
/// \return true if type is a generic Java parameter type, e.g., T in List<T>
inline bool is_java_generic_parameter(const typet &type)
{
  return type.get_bool(ID_C_java_generic_parameter);
}

/// \param type: source type
/// \return cast of type into a java_generic_parametert
inline const java_generic_parametert &to_java_generic_parameter(
  const typet &type)
{
  PRECONDITION(is_java_generic_parameter(type));
  return static_cast<const java_generic_parametert &>(type);
}

/// \param type: source type
/// \return cast of type into a java_generic_parameter
inline java_generic_parametert &to_java_generic_parameter(typet &type)
{
  PRECONDITION(is_java_generic_parameter(type));
  return static_cast<java_generic_parametert &>(type);
}

/// class to hold an instantiated type variable bound is exact, for example the
/// `java.lang.Integer` type in a `List<Integer>`
class java_generic_inst_parametert:public java_generic_parametert
{
public:
  // uses empty name for base type variable java_generic_parametert as real name
  // is not known here
  explicit java_generic_inst_parametert(const typet &type) :
    java_generic_parametert(irep_idt(), type)
  {
    set(ID_C_java_generic_inst_parameter, true);
  }
};

/// \param type: the type to check
/// \return true if type is an instantiated generic Java type, e.g., the Integer
/// in List<Integer>
inline bool is_java_generic_inst_parameter(const typet &type)
{
  return type.get_bool(ID_C_java_generic_inst_parameter);
}

/// \param type: source type
/// \return cast of type into an instantiated java_generic_parameter
inline const java_generic_inst_parametert &to_java_generic_inst_parameter(
  const typet &type)
{
  PRECONDITION(
    type.id()==ID_pointer &&
    is_java_generic_inst_parameter(type));
  return static_cast<const java_generic_inst_parametert &>(type);
}

/// \param type: source type
/// \return cast of type into an instantiated java_generic_inst_parametert
inline java_generic_inst_parametert &to_java_generic_inst_parameter(typet &type)
{
  PRECONDITION(
    type.id()==ID_pointer &&
    is_java_generic_inst_parameter(type));
  return static_cast<java_generic_inst_parametert &>(type);
}

/// class to hold type with generic type variable, for example `java.util.List`
/// in either a reference of type List<Integer> or List<T>. The vector holds
/// the types of the type Variables, that is the vector has the length of the
/// number of type variables of the generic class. For example in `HashMap<K,
/// V>` it would contain two elements, each of type `java_generic_parametert`,
/// in `HashMap<Integer, V>` it would contains two elements, the first of type
/// `java_generic_inst_parametert` and the second of type
/// `java_generic_parametert`.
class java_generic_typet:public reference_typet
{
public:
  typedef std::vector<java_generic_parametert> generic_type_variablest;

  explicit java_generic_typet(const typet &_type) :
    reference_typet(_type, config.ansi_c.pointer_width)
  {
    set(ID_C_java_generic_type, true);
  }


  /// \return vector of type variables
  const generic_type_variablest &generic_type_variables() const
  {
    return (const generic_type_variablest &)(find(ID_type_variables).get_sub());
  }

  /// \return vector of type variables
  generic_type_variablest &generic_type_variables()
  {
    return (generic_type_variablest &)(add(ID_type_variables).get_sub());
  }
};


/// \param type: the type to check
/// \return true if type is java type containing with generics, e.g., List<T>
inline bool is_java_generic_type(const typet &type)
{
  return type.get_bool(ID_C_java_generic_type);
}

/// \param type: source type
/// \return cast of type into java type with generics
inline const java_generic_typet &to_java_generic_type(
  const typet &type)
{
  PRECONDITION(
    type.id()==ID_pointer &&
    is_java_generic_type(type));
  return static_cast<const java_generic_typet &>(type);
}

/// \param type: source type
/// \return cast of type into java type with generics
inline java_generic_typet &to_java_generic_type(typet &type)
{
  PRECONDITION(
    type.id()==ID_pointer &&
    is_java_generic_type(type));
  return static_cast<java_generic_typet &>(type);
}

/// Class to hold a class with generics, extends the java class type with a
/// vector of java_generic_type variables.
///
/// For example, a class definition `class MyGenericClass<T>`
class java_generics_class_typet:public java_class_typet
{
 public:
  typedef std::vector<java_generic_parametert> generic_typest;

  java_generics_class_typet()
  {
    set(ID_C_java_generics_class_type, true);
  }

  const generic_typest &generic_types() const
  {
    return (const generic_typest &)(find(ID_generic_types).get_sub());
  }

  generic_typest &generic_types()
  {
    return (generic_typest &)(add(ID_generic_types).get_sub());
  }
};

/// \param type: the type to check
/// \return true if type is a java class type with generics
inline bool is_java_generics_class_type(const typet &type)
{
  return type.get_bool(ID_C_java_generics_class_type);
}

/// \param type: the type to check
/// \return cast of type to java_generics_class_typet
inline const java_generics_class_typet &to_java_generics_class_type(
  const java_class_typet &type)
{
  PRECONDITION(is_java_generics_class_type(type));
  return static_cast<const java_generics_class_typet &>(type);
}

/// \param type: source type
/// \return cast of type into a java class type with generics
inline java_generics_class_typet &to_java_generics_class_type(
  java_class_typet &type)
{
  PRECONDITION(is_java_generics_class_type(type));
  return static_cast<java_generics_class_typet &>(type);
}

/// Access information of instantiated type params of java instantiated type.
/// \param index: the index of the type variable
/// \param type: the type from which to extract the type variable
/// \return the type variable of t at the given index
inline const typet &java_generic_get_inst_type(
  size_t index,
  const java_generic_typet &type)
{
  const std::vector<java_generic_parametert> &gen_types=
    type.generic_type_variables();
  PRECONDITION(index<gen_types.size());
  return gen_types[index];
}

/// Access information of type variables of a generic java class type.
/// \param index: the index of the type variable
/// \param type: the type from which to extract the type variable
/// \return the name of the generic type variable of t at the given index
inline const irep_idt &java_generics_class_type_var(
  size_t index,
  const java_generics_class_typet &type)
{
  const std::vector<java_generic_parametert> &gen_types=type.generic_types();

  PRECONDITION(index<gen_types.size());
  const java_generic_parametert &gen_type=gen_types[index];

  return gen_type.type_variable().get_identifier();
}

/// Access information of the type bound of a generic java class type.
/// \param index: the index of the type variable
/// \param t: the type from which to extract the type bound
/// \return the type of the bound of the type variable
inline const typet &java_generics_class_type_bound(
  size_t index,
  const typet &t)
{
  PRECONDITION(is_java_generics_class_type(t));
  const java_generics_class_typet &type=
    to_java_generics_class_type(to_java_class_type(t));
  const std::vector<java_generic_parametert> &gen_types=type.generic_types();

  PRECONDITION(index<gen_types.size());
  const java_generic_parametert &gen_type=gen_types[index];

  return gen_type.subtype();
}

#endif // CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

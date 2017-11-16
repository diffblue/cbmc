/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_TYPES_H
#define CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

#include <util/invariant.h>
#include <algorithm>

#include <util/type.h>
#include <util/std_types.h>
#include <util/c_types.h>
#include <util/optional.h>

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
typet java_array_element_type(const symbol_typet &array_type);

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
  const std::string &class_name_prefix="");
char java_char_from_type(const typet &type);
std::vector<typet> java_generic_type_from_string(
  const std::string &,
  const std::string &);

typet java_bytecode_promotion(const typet &);
exprt java_bytecode_promotion(const exprt &);

bool is_java_array_tag(const irep_idt &tag);
bool is_valid_java_array(const struct_typet &);

/// Class to hold a Java generic type parameter (also called type variable),
/// e.g., `T` in `List<T>`.
/// The bound can specify type requirements.
class java_generic_parametert:public reference_typet
{
public:
  typedef symbol_typet type_variablet;

  java_generic_parametert(
    const irep_idt &_type_var_name,
    const symbol_typet &_bound):
    reference_typet(java_reference_type(_bound))
  {
    set(ID_C_java_generic_parameter, true);
    type_variables().push_back(symbol_typet(_type_var_name));
  }

  /// \return the type variable as symbol type
  const type_variablet &type_variable() const
  {
    PRECONDITION(!type_variables().empty());
    return type_variables().front();
  }

private:
  typedef std::vector<type_variablet> type_variablest;
  const type_variablest &type_variables() const
  {
    return (const type_variablest &)(find(ID_type_variables).get_sub());
  }

  type_variablest &type_variables()
  {
    return (type_variablest &)(add(ID_type_variables).get_sub());
  }
};

/// Checks whether the type is a java generic parameter/variable, e.g., `T` in
/// `List<T>`.
/// \param type: the type to check
/// \return true if type is a generic Java parameter type
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

/// Class to hold type with generic type arguments, for example `java.util.List`
/// in either a reference of type List<Integer> or List<T> (here T must have
/// been concretized already to create this object so technically it is an
/// argument rather than parameter/variable, but in the symbol table this still
/// shows as the parameter T). The vector holds the types of the type arguments
/// (all of type or subtype of reference_typet), that is the vector has
/// the length of the number of type parameters of the generic class.
/// For example:
/// - in `HashMap<K, V>` it would contain two elements, each of type
///   `java_generic_parametert`,
/// - in `HashMap<Integer, V>` it would contain two elements, the first of type
///   `reference_typet` and the second of type `java_generic_parametert`,
/// - in `HashMap<List<T>, V>` it would contain two elements, the first of
///   type `java_generic_typet` and the second of type
///   `java_generic_parametert`.
class java_generic_typet:public reference_typet
{
public:
  typedef std::vector<reference_typet> generic_type_argumentst;

  explicit java_generic_typet(const typet &_type):
    reference_typet(java_reference_type(_type))
  {
    set(ID_C_java_generic_type, true);
  }

  /// \return vector of type variables
  const generic_type_argumentst &generic_type_arguments() const
  {
    return (const generic_type_argumentst &)(
      find(ID_type_variables).get_sub());
  }

  /// \return vector of type variables
  generic_type_argumentst &generic_type_arguments()
  {
    return (generic_type_argumentst &)(
      add(ID_type_variables).get_sub());
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
/// vector of java generic type parameters (also called type variables). For
/// example, a class definition `class MyGenericClass<T>`.
class java_generic_class_typet:public java_class_typet
{
 public:
  typedef std::vector<java_generic_parametert> generic_typest;

  java_generic_class_typet()
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
inline bool is_java_generic_class_type(const typet &type)
{
  return type.get_bool(ID_C_java_generics_class_type);
}

/// \param type: the type to check
/// \return cast of type to java_generics_class_typet
inline const java_generic_class_typet &
to_java_generic_class_type(const java_class_typet &type)
{
  PRECONDITION(is_java_generic_class_type(type));
  return static_cast<const java_generic_class_typet &>(type);
}

/// \param type: source type
/// \return cast of type into a java class type with generics
inline java_generic_class_typet &
to_java_generic_class_type(java_class_typet &type)
{
  PRECONDITION(is_java_generic_class_type(type));
  return static_cast<java_generic_class_typet &>(type);
}

/// Access information of type arguments of java instantiated type.
/// \param index: the index of the type argument
/// \param type: the type from which to extract the type argument
/// \return the type variable of t at the given index
inline const typet &java_generic_get_inst_type(
  size_t index,
  const java_generic_typet &type)
{
  const std::vector<reference_typet> &type_arguments =
    type.generic_type_arguments();
  PRECONDITION(index<type_arguments.size());
  return type_arguments[index];
}

/// Access information of type variables of a generic java class type.
/// \param index: the index of the type variable
/// \param type: the type from which to extract the type variable
/// \return the name of the generic type variable of t at the given index
inline const irep_idt &
java_generic_class_type_var(size_t index, const java_generic_class_typet &type)
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
inline const typet &java_generic_class_type_bound(size_t index, const typet &t)
{
  PRECONDITION(is_java_generic_class_type(t));
  const java_generic_class_typet &type =
    to_java_generic_class_type(to_java_class_type(t));
  const std::vector<java_generic_parametert> &gen_types=type.generic_types();

  PRECONDITION(index<gen_types.size());
  const java_generic_parametert &gen_type=gen_types[index];

  return gen_type.subtype();
}

/// An exception that is raised for unsupported class signature.
/// Currently we do not parse multiple bounds.
class unsupported_java_class_signature_exceptiont:public std::logic_error
{
public:
  explicit unsupported_java_class_signature_exceptiont(std::string type):
    std::logic_error(
      "Unsupported class signature: "+type)
  {
  }
};

inline typet java_type_from_string_with_exception(
  const std::string &descriptor,
  const optionalt<std::string> &signature,
  const std::string &class_name)
{
  try
  {
    return java_type_from_string(signature.value(), class_name);
  }
  catch(unsupported_java_class_signature_exceptiont &)
  {
    return java_type_from_string(descriptor, class_name);
  }
}

/// Get the index in the subtypes array for a given component.
/// \param t The type we search for the subtypes in.
/// \param identifier The string identifier of the type of the component.
/// \return Optional with the size if the identifier was found.
inline const optionalt<size_t> java_generics_get_index_for_subtype(
  const java_generic_class_typet &t,
  const irep_idt &identifier)
{
  const std::vector<java_generic_parametert> &gen_types=
    t.generic_types();

  const auto iter = std::find_if(
    gen_types.cbegin(),
    gen_types.cend(),
    [&identifier](const java_generic_parametert &ref)
    {
      return ref.type_variable().get_identifier()==identifier;
    });

  if(iter==gen_types.cend())
  {
    return {};
  }

  return std::distance(gen_types.cbegin(), iter);
}

class java_specialised_generic_class_typet : public java_class_typet
{
  // note the constructor could take the components and construct it itself
  // note vector of generic parameter of symbol type
public:
  // TODO: to be defined more appropriately.
  java_specialised_generic_class_typet()
  {
    set(ID_C_specialised_generic_java_class, true);
  }
};

inline const bool java_is_specialised_generic_class_type(const typet &type)
{
  return type.get_bool(ID_C_specialised_generic_java_class);
}

inline java_specialised_generic_class_typet
to_java_specialised_class_typet(const typet &type)
{
  INVARIANT(java_is_specialised_generic_class_type(type),
            "Tried to convert a type that was not a specialised generic java class");
  return static_cast<const java_specialised_generic_class_typet &>(type);
}

#endif // CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

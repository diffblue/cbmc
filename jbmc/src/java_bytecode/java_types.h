/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_TYPES_H
#define CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

#include <util/invariant.h>
#include <algorithm>
#include <set>

#include <util/type.h>
#include <util/std_types.h>
#include <util/c_types.h>
#include <util/optional.h>
#include <util/std_expr.h>

class java_annotationt : public irept
{
public:
  class valuet : public irept
  {
  public:
    valuet(irep_idt name, const exprt &value) : irept(name)
    {
      get_sub().push_back(value);
    }

    const irep_idt &get_name() const
    {
      return id();
    }

    const exprt &get_value() const
    {
      return static_cast<const exprt &>(get_sub().front());
    }
  };

  explicit java_annotationt(const typet &type)
  {
    set(ID_type, type);
  }

  const typet &get_type() const
  {
    return static_cast<const typet &>(find(ID_type));
  }

  const std::vector<valuet> &get_values() const
  {
    // This cast should be safe as valuet doesn't add data to irept
    return reinterpret_cast<const std::vector<valuet> &>(get_sub());
  }

  std::vector<valuet> &get_values()
  {
    // This cast should be safe as valuet doesn't add data to irept
    return reinterpret_cast<std::vector<valuet> &>(get_sub());
  }
};

class annotated_typet : public typet
{
public:
  const std::vector<java_annotationt> &get_annotations() const
  {
    // This cast should be safe as java_annotationt doesn't add data to irept
    return reinterpret_cast<const std::vector<java_annotationt> &>(
      find(ID_C_annotations).get_sub());
  }

  std::vector<java_annotationt> &get_annotations()
  {
    // This cast should be safe as java_annotationt doesn't add data to irept
    return reinterpret_cast<std::vector<java_annotationt> &>(
      add(ID_C_annotations).get_sub());
  }
};

inline const annotated_typet &to_annotated_type(const typet &type)
{
  return static_cast<const annotated_typet &>(type);
}

inline annotated_typet &to_annotated_type(typet &type)
{
  return static_cast<annotated_typet &>(type);
}

template <>
inline bool can_cast_type<annotated_typet>(const typet &)
{
  return true;
}

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

  bool get_is_inner_class() const
  {
    return get_bool(ID_is_inner_class);
  }

  void set_is_inner_class(const bool &is_inner_class)
  {
    return set(ID_is_inner_class, is_inner_class);
  }

  const irep_idt &get_outer_class() const
  {
    return get(ID_outer_class);
  }

  void set_outer_class(const irep_idt &outer_class)
  {
    return set(ID_outer_class, outer_class);
  }

  const irep_idt &get_super_class() const
  {
    return get(ID_super_class);
  }

  void set_super_class(const irep_idt &super_class)
  {
    return set(ID_super_class, super_class);
  }

  bool get_is_static_class() const
  {
    return get_bool(ID_is_static);
  }

  void set_is_static_class(const bool &is_static_class)
  {
    return set(ID_is_static, is_static_class);
  }

  bool get_is_anonymous_class() const
  {
    return get_bool(ID_is_anonymous);
  }

  void set_is_anonymous_class(const bool &is_anonymous_class)
  {
    return set(ID_is_anonymous, is_anonymous_class);
  }

  bool get_final() const
  {
    return get_bool(ID_final);
  }

  void set_final(bool is_final)
  {
    set(ID_final, is_final);
  }

  typedef std::vector<symbol_exprt> java_lambda_method_handlest;

  const java_lambda_method_handlest &lambda_method_handles() const
  {
    return (const java_lambda_method_handlest &)find(
             ID_java_lambda_method_handles)
      .get_sub();
  }

  java_lambda_method_handlest &lambda_method_handles()
  {
    return (java_lambda_method_handlest &)add(ID_java_lambda_method_handles)
      .get_sub();
  }

  void add_lambda_method_handle(const irep_idt &identifier)
  {
    // creates a symbol_exprt for the identifier and pushes it in the vector
    lambda_method_handles().emplace_back(identifier);
  }
  void add_unknown_lambda_method_handle()
  {
    // creates empty symbol_exprt and pushes it in the vector
    lambda_method_handles().emplace_back();
  }

  const std::vector<java_annotationt> &get_annotations() const
  {
    return static_cast<const annotated_typet &>(
      static_cast<const typet &>(*this)).get_annotations();
  }

  std::vector<java_annotationt> &get_annotations()
  {
    return type_checked_cast<annotated_typet>(
      static_cast<typet &>(*this)).get_annotations();
  }

  /// Get the name of the struct, which can be used to look up its symbol
  /// in the symbol table.
  const irep_idt &get_name() const
  {
    return get(ID_name);
  }

  /// Set the name of the struct, which can be used to look up its symbol
  /// in the symbol table.
  void set_name(const irep_idt &name)
  {
    set(ID_name, name);
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

template <>
inline bool can_cast_type<java_class_typet>(const typet &type)
{
  return can_cast_type<class_typet>(type);
}

class java_method_typet : public code_typet
{
public:
  using code_typet::parameterst;
  using code_typet::parametert;

  /// Constructs a new code type, i.e. method type
  /// \param _parameters: the vector of method parameters
  /// \param _return_type: the return type
  java_method_typet(parameterst &&_parameters, typet &&_return_type)
    : code_typet(std::move(_parameters), std::move(_return_type))
  {
    set(ID_C_java_method_type, true);
  }

  /// Constructs a new code type, i.e. method type
  /// \param _parameters: the vector of method parameters
  /// \param _return_type: the return type
  java_method_typet(parameterst &&_parameters, const typet &_return_type)
    : code_typet(std::move(_parameters), _return_type)
  {
    set(ID_C_java_method_type, true);
  }

  const std::vector<irep_idt> throws_exceptions() const
  {
    std::vector<irep_idt> exceptions;
    for(const auto &e : find(ID_exceptions_thrown_list).get_sub())
      exceptions.push_back(e.id());
    return exceptions;
  }

  void add_throws_exceptions(irep_idt exception)
  {
    add(ID_exceptions_thrown_list).get_sub().push_back(irept(exception));
  }

  bool get_is_final() const
  {
    return get_bool(ID_final);
  }

  void set_is_final(bool is_final)
  {
    set(ID_final, is_final);
  }

  bool get_native() const
  {
    return get_bool(ID_is_native_method);
  }

  void set_native(bool is_native)
  {
    set(ID_is_native_method, is_native);
  }

  bool get_is_varargs() const
  {
    return get_bool(ID_is_varargs_method);
  }

  void set_is_varargs(bool is_varargs)
  {
    set(ID_is_varargs_method, is_varargs);
  }
};

template <>
inline bool can_cast_type<java_method_typet>(const typet &type)
{
  return type.id() == ID_code && type.get_bool(ID_C_java_method_type);
}

inline const java_method_typet &to_java_method_type(const typet &type)
{
  PRECONDITION(can_cast_type<java_method_typet>(type));
  return static_cast<const java_method_typet &>(type);
}

inline java_method_typet &to_java_method_type(typet &type)
{
  PRECONDITION(can_cast_type<java_method_typet>(type));
  return static_cast<java_method_typet &>(type);
}

typet java_int_type();
typet java_long_type();
typet java_short_type();
typet java_byte_type();
typet java_char_type();
typet java_float_type();
typet java_double_type();
typet java_boolean_type();
typet java_void_type();
reference_typet java_reference_type(const typet &subtype);
reference_typet java_lang_object_type();
symbol_typet java_classname(const std::string &);

reference_typet java_array_type(const char subtype);
const typet &java_array_element_type(const symbol_typet &array_symbol);
typet &java_array_element_type(symbol_typet &array_symbol);
bool is_java_array_type(const typet &type);
bool is_multidim_java_array_type(const typet &type);

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
size_t find_closing_semi_colon_for_reference_type(
  const std::string src,
  size_t starting_point = 0);


bool is_java_array_tag(const irep_idt &tag);
bool is_valid_java_array(const struct_typet &);

bool equal_java_types(const typet &type1, const typet &type2);

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

  type_variablet &type_variable_ref()
  {
    PRECONDITION(!type_variables().empty());
    return const_cast<type_variablet &>(type_variables().front());
  }

  const irep_idt get_name() const
  {
    return type_variable().get_identifier();
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

template <>
inline bool can_cast_type<java_generic_typet>(const typet &type)
{
  return is_reference(type) && type.get_bool(ID_C_java_generic_type);
}

/// \param type: the type to check
/// \return true if type is java type containing with generics, e.g., List<T>
inline bool is_java_generic_type(const typet &type)
{
  return can_cast_type<java_generic_typet>(type);
}

/// \param type: source type
/// \return cast of type into java type with generics
inline const java_generic_typet &to_java_generic_type(
  const typet &type)
{
  PRECONDITION(can_cast_type<java_generic_typet>(type));
  return static_cast<const java_generic_typet &>(type);
}

/// \param type: source type
/// \return cast of type into java type with generics
inline java_generic_typet &to_java_generic_type(typet &type)
{
  PRECONDITION(can_cast_type<java_generic_typet>(type));
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

/// Type to hold a Java class that is implicitly generic, e.g., an inner
/// class of a generic outer class or a derived class of a generic base
/// class. Extends the java class type.
class java_implicitly_generic_class_typet : public java_class_typet
{
public:
  typedef std::vector<java_generic_parametert> implicit_generic_typest;

  explicit java_implicitly_generic_class_typet(
    const java_class_typet &class_type,
    const implicit_generic_typest &generic_types)
    : java_class_typet(class_type)
  {
    set(ID_C_java_implicitly_generic_class_type, true);
    for(const auto &type : generic_types)
    {
      implicit_generic_types().push_back(type);
    }
  }

  const implicit_generic_typest &implicit_generic_types() const
  {
    return (
      const implicit_generic_typest
        &)(find(ID_implicit_generic_types).get_sub());
  }

  implicit_generic_typest &implicit_generic_types()
  {
    return (
      implicit_generic_typest &)(add(ID_implicit_generic_types).get_sub());
  }
};

/// \param type: the type to check
/// \return true if type is a implicitly generic java class type
inline bool is_java_implicitly_generic_class_type(const typet &type)
{
  return type.get_bool(ID_C_java_implicitly_generic_class_type);
}

/// \param type: the type to check
/// \return cast of type to java_generics_class_typet
inline const java_implicitly_generic_class_typet &
to_java_implicitly_generic_class_type(const java_class_typet &type)
{
  PRECONDITION(is_java_implicitly_generic_class_type(type));
  return static_cast<const java_implicitly_generic_class_typet &>(type);
}

/// \param type: source type
/// \return cast of type into a java class type with generics
inline java_implicitly_generic_class_typet &
to_java_implicitly_generic_class_type(java_class_typet &type)
{
  PRECONDITION(is_java_implicitly_generic_class_type(type));
  return static_cast<java_implicitly_generic_class_typet &>(type);
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
/// \param gen_types: The subtypes array.
/// \param identifier: The string identifier of the type of the component.
/// \return Optional with the size if the identifier was found.
inline const optionalt<size_t> java_generics_get_index_for_subtype(
  const std::vector<java_generic_parametert> &gen_types,
  const irep_idt &identifier)
{
  const auto iter = std::find_if(
    gen_types.cbegin(),
    gen_types.cend(),
    [&identifier](const java_generic_parametert &ref)
    {
      return ref.type_variable().get_identifier() == identifier;
    });

  if(iter == gen_types.cend())
  {
    return {};
  }

  return std::distance(gen_types.cbegin(), iter);
}

void get_dependencies_from_generic_parameters(
  const std::string &,
  std::set<irep_idt> &);
void get_dependencies_from_generic_parameters(
  const typet &,
  std::set<irep_idt> &);

/// Type for a generic symbol, extends symbol_typet with a
/// vector of java generic types.
/// This is used to store the type of generic superclasses and interfaces.
class java_generic_symbol_typet : public symbol_typet
{
public:
  typedef std::vector<reference_typet> generic_typest;

  java_generic_symbol_typet(
    const symbol_typet &type,
    const std::string &base_ref,
    const std::string &class_name_prefix);

  const generic_typest &generic_types() const
  {
    return (const generic_typest &)(find(ID_generic_types).get_sub());
  }

  generic_typest &generic_types()
  {
    return (generic_typest &)(add(ID_generic_types).get_sub());
  }

  optionalt<size_t>
  generic_type_index(const java_generic_parametert &type) const;
};

/// \param type: the type to check
/// \return true if the type is a symbol type with generics
inline bool is_java_generic_symbol_type(const typet &type)
{
  return type.get_bool(ID_C_java_generic_symbol);
}

/// \param type: the type to convert
/// \return the converted type
inline const java_generic_symbol_typet &
to_java_generic_symbol_type(const typet &type)
{
  PRECONDITION(is_java_generic_symbol_type(type));
  return static_cast<const java_generic_symbol_typet &>(type);
}

/// \param type: the type to convert
/// \return the converted type
inline java_generic_symbol_typet &to_java_generic_symbol_type(typet &type)
{
  PRECONDITION(is_java_generic_symbol_type(type));
  return static_cast<java_generic_symbol_typet &>(type);
}

/// Take a signature string and remove everything in angle brackets allowing for
/// the type to be parsed normally, for example
/// `java.util.HashSet<java.lang.Integer>` will be turned into
/// `java.util.HashSet`
std::string erase_type_arguments(const std::string &);
/// Returns the full class name, skipping over the generics. This turns any of
/// these:
///   1. Signature: Lcom/package/OuterClass<TT;>.Inner;
///   2. Descriptor: Lcom.pacakge.OuterClass$Inner;
/// into `com.package.OuterClass.Inner`
std::string gather_full_class_name(const std::string &);

// turn java type into string
std::string pretty_java_type(const typet &);

// pretty signature for methods
std::string pretty_signature(const java_method_typet &);

#endif // CPROVER_JAVA_BYTECODE_JAVA_TYPES_H

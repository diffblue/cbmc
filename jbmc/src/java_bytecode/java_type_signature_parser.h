// Copyright 2019 Diffblue Limited.

/// \file
/// Parser for Java type signatures

#ifndef CPROVER_JAVA_BYTECODE_JAVA_TYPE_SIGNATURE_PARSER_H
#define CPROVER_JAVA_BYTECODE_JAVA_TYPE_SIGNATURE_PARSER_H

#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include <util/type.h>

class java_generic_type_parametert;
typedef
  std::unordered_map<std::string, std::shared_ptr<java_generic_type_parametert>>
  java_generic_type_parameter_mapt;

/// Base class for parsed type signatures
class java_type_signaturet
{
public:
  virtual ~java_type_signaturet() = default;

  /// Gather the names of classes referred to by this type
  /// \param deps A set into which to gether the names of classes referred to
  ///   by this type
  virtual void collect_class_dependencies(std::set<irep_idt> &deps) const = 0;

  /// Get the typet representation of this type
  /// \param class_name_prefix The prefix to put before the class name to make
  ///   the full name for a class used in its typet representation
  /// \return The typet representation of this type
  /// \remarks This may lose information where typet doesn't currently support
  ///   all the features of java
  virtual typet get_type(const std::string &class_name_prefix) const = 0;

  /// Output this type in human readable (Java) format
  /// \param stm The stream to which to output
  virtual void output(std::ostream &stm) const = 0;
};

/// Operator<< overload to output a parsed type signature to a stream
/// \param stm The stream to which to output
/// \param me The parsed type signature to output
/// \return The stream passed as input
inline std::ostream &
operator<<(std::ostream &stm, const java_type_signaturet &me)
{
  me.output(stm);
  return stm;
}

/// Base class for parsed type signatures representing the type of a value
class java_value_type_signaturet : public java_type_signaturet
{
public:
  /// Static method to parse a java_value_type_signaturet from a type signature
  /// \param type_string The type signature to parse
  /// \param parameter_map A map giving the parameters in scope for this
  ///   signature
  /// \return The parsed java_value_type_signaturet
  static std::shared_ptr<java_value_type_signaturet> parse_single_value_type(
    const std::string &type_string,
    const java_generic_type_parameter_mapt &parameter_map);
};

/// A list of type signatures, typically used for the types of type parameter
/// bounds, generic type arguments or implemented interfaces
typedef std::vector<std::shared_ptr<java_value_type_signaturet>>
  java_type_signature_listt;

/// Operator<< overload to output a list of parsed type signatures to a stream
/// \param stm The stream to which to output
/// \param types The list of parsed type signatures to output
/// \return The stream passed as input
std::ostream &
operator<<(std::ostream &stm, const java_type_signature_listt &types);

/// A generic type parameter, this class is used to represent both their
/// declarations and their usages
class java_generic_type_parametert : public java_value_type_signaturet
{
public:
  /// The name of the parameter, empty for a wildcard type
  const std::string name;
  /// Bound on the type parameter that is a class
  /// \remarks
  /// If there isn't one then there must be at least one interface bound
  /// If no bound is explicitly specified this this will be java.lang.Object
  std::shared_ptr<java_value_type_signaturet> class_bound;
  /// Bounds on the type parameter that are interfaces
  /// \remarks
  /// If there aren't any then there must be a class bound
  java_type_signature_listt interface_bounds;

  /// Whether the bounds are upper bounds rather than lower bounds
  bool bounds_are_upper;

  // Delete the copy constructor - the declaration and the usage should share
  // the same object
  java_generic_type_parametert(const java_generic_type_parametert &) = delete;
  java_generic_type_parametert(java_generic_type_parametert &&) = default;

  /// Create a wildcard type parameter
  java_generic_type_parametert();

  /// Create a wildcard type parameter with bounds
  /// \param bounds_are_upper Whether the bounds to be added will be upper
  ///   bounds
  explicit java_generic_type_parametert(bool bounds_are_upper)
    : bounds_are_upper(bounds_are_upper)
  {
  }

  /// Create a named type parameter
  /// \param name The name of the type parameter to create
  explicit java_generic_type_parametert(std::string name)
    : name(std::move(name)), bounds_are_upper(true)
  {
  }

  /// Get whether this is a wildcard type parameter
  /// \return Whether this is a wildcard type parameter
  bool is_wild() const
  {
    return name.empty();
  }

  /// Gather the names of classes referred to by this parameter at the point
  ///   where it is used
  /// \param deps A set into which to gether the names of classes referred to
  ///   by this type
  void collect_class_dependencies(std::set<irep_idt> &deps) const override
  {
    // Bounds are collected from type parameter declarations except in the case
    // of wildcard bounds
    if(name.empty())
      collect_class_dependencies_from_bounds(deps);
  }

  /// Gather the names of classes referred to by this parameter at the point
  ///   where it is declared
  /// \param deps A set into which to gether the names of classes referred to
  ///   by this type
  void
  collect_class_dependencies_from_declaration(std::set<irep_idt> &deps) const
  {
    // This should only be called on type parameter declarations, not wildcards
    PRECONDITION(!name.empty());
    collect_class_dependencies_from_bounds(deps);
  }

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override
  {
    full_output(stm);
  }
  /// Output this type in human readable (Java) format
  /// \param stm The stream to which to output
  /// \param show_bounds Whether to include the list of bounds in the output
  void full_output(std::ostream &stm, bool show_bounds = false) const;

private:
  /// Gather the names of classes referred to by this parameter
  /// \param deps A set into which to gether the names of classes referred to
  ///   by this type
  void collect_class_dependencies_from_bounds(std::set<irep_idt> &deps) const;
};

/// A vector of type parameters
typedef std::vector<std::shared_ptr<java_generic_type_parametert>>
  java_generic_type_parameter_listt;

/// Operator<< overload to output a list of type parameters to a stream
/// \param stm The stream to which to output
/// \param parameters The list of type parameters to output
/// \return The stream passed as input
std::ostream &operator<<(
  std::ostream &stm,
  const java_generic_type_parameter_listt &parameters);

/// A primitive type, such as int (but not Integer)
class java_primitive_type_signaturet : public java_value_type_signaturet
{
public:
  const char type_character;

  explicit java_primitive_type_signaturet(char type_character)
    : type_character(type_character)
  {
  }

  /// \copydoc java_type_signaturet::collect_class_dependencies
  void collect_class_dependencies(std::set<irep_idt> &deps) const override
  {
  }

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override;
};

/// An array type, specifying the type of the elements
class java_array_type_signaturet : public java_value_type_signaturet
{
public:
  std::shared_ptr<java_value_type_signaturet> element_type;

  explicit java_array_type_signaturet(
    std::shared_ptr<java_value_type_signaturet> element_type)
    : element_type(std::move(element_type))
  {
  }

  /// \copydoc java_type_signaturet::collect_class_dependencies
  void collect_class_dependencies(std::set<irep_idt> &deps) const override;

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override;
};

/// A reference to a class type
class java_ref_type_signaturet : public java_value_type_signaturet
{
public:
  /// The name of the class referred to
  std::string class_name;
  /// Generic type arguments
  java_type_signature_listt type_arguments;
  /// If not nullptr then the reference is to this inner class within the
  /// current class reference
  std::shared_ptr<java_ref_type_signaturet> inner_class;

  java_ref_type_signaturet(const java_ref_type_signaturet &) = delete;
  java_ref_type_signaturet(java_ref_type_signaturet &&) = default;

  java_ref_type_signaturet(
    std::string class_name,
    java_type_signature_listt type_arguments,
    std::shared_ptr<java_ref_type_signaturet> inner_class);

  /// \copydoc java_type_signaturet::collect_class_dependencies
  void collect_class_dependencies(std::set<irep_idt> &deps) const override;

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override;
};

/// Type signature of a class, does not include its name
class java_class_type_signaturet : public java_type_signaturet
{
public:
  /// Base classes, including interfaces
  java_type_signature_listt bases;
  /// Type parameters specified on the class declaration
  java_generic_type_parameter_listt explicit_type_parameters;
  /// Type parameters in scope in the class, including those from outer classes
  java_generic_type_parameter_mapt type_parameter_map;

private:
  /// Private default constructor used by object_type
  java_class_type_signaturet()
  {
  }

public:
  /// Create a java_class_type_signaturet by parsing a type signature
  /// \param type_string The type signature to parse
  /// \param outer_parameter_map A map giving the parameters in scope for this
  ///   signature
  java_class_type_signaturet(
    const std::string &type_string,
    const java_generic_type_parameter_mapt &outer_parameter_map);

  /// The type signature of java.lang.Object
  static const java_class_type_signaturet object_type;

  /// \copydoc java_type_signaturet::collect_class_dependencies
  void collect_class_dependencies(std::set<irep_idt> &deps) const override;

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override;
};

/// Type signature of a method, does not include its name
class java_method_type_signaturet : public java_type_signaturet
{
public:
  /// The types of the parameters to the method
  java_type_signature_listt parameters;
  /// The return type of the method
  std::shared_ptr<java_value_type_signaturet> return_type;
  /// Type parameters specified on the method declaration
  java_generic_type_parameter_listt explicit_type_parameters;
  /// Type parameters in scope in the method, including those from the
  /// containing classes
  java_generic_type_parameter_mapt type_parameter_map;

  /// Create a java_method_type_signaturet by parsing a type signature
  /// \param type_string The type signature to parse
  /// \param class_parameter_map A map giving the parameters in scope for this
  ///   signature
  java_method_type_signaturet(
    const std::string &type_string,
    java_generic_type_parameter_mapt class_parameter_map);

  /// \copydoc java_type_signaturet::collect_class_dependencies
  void collect_class_dependencies(std::set<irep_idt> &deps) const override;

  /// \copydoc java_type_signaturet::get_type
  typet get_type(const std::string &class_name_prefix) const override;

  /// \copydoc java_type_signaturet::output
  void output(std::ostream &stm) const override;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_TYPE_SIGNATURE_PARSER_H

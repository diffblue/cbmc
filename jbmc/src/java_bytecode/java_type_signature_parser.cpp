// Copyright 2019 Diffblue Limited.

/// \file
/// Parser for Java type signatures

#include "java_type_signature_parser.h"
#include <ostream>
#include <util/parsable_string.h>

#include "java_types.h"

///////////////////////////////////////////////////////////
// static parse functions

static std::shared_ptr<java_ref_type_signaturet> parse_class_type(
  parsable_stringt &type_string,
  const java_generic_type_parameter_mapt &parameters);

/// Parse a java_value_type_signaturet from a parsable_stringt pointing at an
/// appropriate part of a type signature
/// \param type_string A parsable_stringt pointing at an appropriate part of a
///   type signature
/// \param parameters A map giving the parameters in scope for this signature
/// \return The parsed java_value_type_signaturet
static std::shared_ptr<java_value_type_signaturet> parse_type(
  parsable_stringt &type_string,
  const java_generic_type_parameter_mapt &parameters)
{
  char first =
    type_string.get_first("Expected type string at end of signature");
  switch(first)
  {
  case 'B':
  case 'F':
  case 'D':
  case 'I':
  case 'C':
  case 'S':
  case 'Z':
  case 'V':
  case 'J':
    return std::make_shared<java_primitive_type_signaturet>(first);
  case '[':
    return std::make_shared<java_array_type_signaturet>(
      parse_type(type_string, parameters));
  case 'L': // Class type
    return parse_class_type(type_string, parameters);
  case 'T': // Type parameter
  {
    parsable_stringt parameter_name = type_string.split_at_first(
      ';', "Type parameter reference doesn't have closing semicolon");
    auto parameter = parameters.find(parameter_name);
    if(parameter == parameters.end())
      throw parse_exceptiont(
        "Reference to undefined type parameter: " +
          std::string(parameter_name));
    return parameter->second;
  }
  case '*':
  case '+':
  case '-':
    throw unsupported_java_class_signature_exceptiont("Wild card generic");
  default:
    throw unsupported_java_class_signature_exceptiont(
      std::string("Unknown type signature starting with ") + first);
  }
}

/// Parse the signature of a reference to a class type
/// \param type_string A parsable_stringt starting at the type signature of a
///   reference to a class
/// \param parameters The generic type parameters that may appear in the type
/// \return The parsed type
static std::shared_ptr<java_ref_type_signaturet> parse_class_type(
  parsable_stringt &type_string,
  const java_generic_type_parameter_mapt &parameters)
{
  // Check if a < occurs before a ;
  std::pair<parsable_stringt, char> class_name_and_next =
    type_string.split_at_first_of(
      "<;", "Class type doesn't have closing semicolon");
  java_type_signature_listt type_arguments;
  if(class_name_and_next.second == '<')
  {
    do
    {
      type_arguments.push_back(parse_type(type_string, parameters));
    } while(!type_string.try_skip('>'));
    type_string.skip(
      ';', "Class type with type arguments doesn't have closing semicolon");
  }
  return std::make_shared<java_ref_type_signaturet>(
    class_name_and_next.first, std::move(type_arguments));
}

/// Parse a reference to a generic type parameter
/// \param parameter_string A parsable_stringt starting at the type signature
///   of a type parameter
/// \return The parsed type parameter
static std::shared_ptr<java_generic_type_parametert>
parse_type_parameter(parsable_stringt &parameter_string)
{
  std::shared_ptr<java_generic_type_parametert> result =
    std::make_shared<java_generic_type_parametert>(
      parameter_string.split_at_first(':', "No colon in type parameter bound"));
  java_generic_type_parameter_mapt parameter_map;
  // Allow recursive definitions where the bound refers to the parameter itself
  parameter_map.emplace(result->name, result);
  if(!parameter_string.starts_with(':'))
    result->class_bound = parse_type(parameter_string, parameter_map);
  while(parameter_string.try_skip(':'))
  {
    result->interface_bounds.push_back(
      parse_type(parameter_string, parameter_map));
  }
  INVARIANT(
    result->class_bound != nullptr || !result->interface_bounds.empty(),
    "All type parameters have at least one bound");
  return result;
}

/// Parse an optional collection of formal type parameters (e.g. on generic
/// methods of non-generic classes, generic static methods or generic classes).
/// \param parameters_string A parsable_stringt starting at where the
///   collection would appear
/// \return The parsed java_generic_type_parameter_listt
/// \example
/// This java method: static void <T, U extends V> foo(T t, U u, int x)
/// Would have this signature: <T:Ljava/lang/Object;U:LV;>(TT;TU;I)V
static java_generic_type_parameter_listt
parse_type_parameters(parsable_stringt &parameters_string)
{
  java_generic_type_parameter_listt parameter_map;
  if(parameters_string.try_skip('<'))
  {
    do
    {
      parameter_map.push_back(parse_type_parameter(parameters_string));
    } while(!parameters_string.try_skip('>'));
  }
  return parameter_map;
}


///////////////////////////////////////////////////////////
// java_type_signaturet derivatives

std::shared_ptr<java_value_type_signaturet>
java_value_type_signaturet::parse_single_value_type(
  const std::string &type_string,
  const java_generic_type_parameter_mapt &parameter_map)
{
  parsable_stringt type_str = type_string;
  std::shared_ptr<java_value_type_signaturet> type =
    parse_type(type_str, parameter_map);
  if(!type_str.empty())
    throw parse_exceptiont("Extra content after type signature");
  return type;
}

std::ostream &
operator<<(std::ostream &stm, const java_type_signature_listt &types)
{
  bool first = true;
  for(const std::shared_ptr<java_value_type_signaturet> &type : types)
  {
    if(!first)
      stm << ", ";
    else
      first = false;
    stm << *type;
  }
  return stm;
}

typet java_generic_type_parametert::get_type(
  const std::string &class_name_prefix) const
{
  return java_generic_parametert(
    class_name_prefix + "::" + name,
    to_struct_tag_type(
      // We currently only support one bound per variable, use the first
      (class_bound != nullptr ? class_bound : interface_bounds[0])
        ->get_type(class_name_prefix)
        .subtype()));
}

void java_generic_type_parametert::full_output(
  std::ostream &stm,
  bool show_bounds) const
{
  stm << name;
  if(show_bounds)
  {
    stm << " extends ";
    bool first = true;
    if(class_bound != nullptr)
    {
      stm << *class_bound;
      first = false;
    }
    for(const std::shared_ptr<java_value_type_signaturet> &interface_bound :
        interface_bounds)
    {
      if(!first)
        stm << " & ";
      else
        first = false;
      stm << *interface_bound;
    }
  }
}

void java_generic_type_parametert::collect_class_dependencies_from_declaration(
  std::set<irep_idt> &deps) const
{
  if(class_bound != nullptr)
    class_bound->collect_class_dependencies(deps);
  for(const std::shared_ptr<java_value_type_signaturet> &interface_bound :
      interface_bounds)
  {
    interface_bound->collect_class_dependencies(deps);
  }
}

typet java_primitive_type_signaturet::get_type(
  const std::string &class_name_prefix) const
{
  switch(type_character)
  {
  case 'B':
    return java_byte_type();
  case 'F':
    return java_float_type();
  case 'D':
    return java_double_type();
  case 'I':
    return java_int_type();
  case 'C':
    return java_char_type();
  case 'S':
    return java_short_type();
  case 'Z':
    return java_boolean_type();
  case 'V':
    return java_void_type();
  case 'J':
    return java_long_type();
  default:
    UNREACHABLE;
  }
}

void java_primitive_type_signaturet::output(std::ostream &stm) const
{
  switch(type_character)
  {
  case 'B':
    stm << "byte";
    break;
  case 'F':
    stm << "float";
    break;
  case 'D':
    stm << "double";
    break;
  case 'I':
    stm << "int";
    break;
  case 'C':
    stm << "char";
    break;
  case 'S':
    stm << "short";
    break;
  case 'Z':
    stm << "boolean";
    break;
  case 'V':
    stm << "void";
    break;
  case 'J':
    stm << "long";
    break;
  default:
    UNREACHABLE;
  }
}

void java_array_type_signaturet::collect_class_dependencies(
  std::set<irep_idt> &deps) const
{
  element_type->collect_class_dependencies(deps);
}

typet java_array_type_signaturet::get_type(
  const std::string &class_name_prefix) const
{
  // If this is a reference array, we generate a plain array[reference]
  // with void* members, but note the real type in ID_C_element_type.
  std::shared_ptr<java_primitive_type_signaturet> primitive_elt_type =
    std::dynamic_pointer_cast<java_primitive_type_signaturet>(element_type);
  typet result = java_array_type(static_cast<char>(std::tolower(
    primitive_elt_type == nullptr ? 'A' : primitive_elt_type->type_character)));
  result.subtype().set(
    ID_element_type, element_type->get_type(class_name_prefix));
  return result;
}

void java_array_type_signaturet::output(std::ostream &stm) const
{
  stm << *element_type << "[]";
}

java_ref_type_signaturet::java_ref_type_signaturet(
  std::string class_name,
  java_type_signature_listt type_arguments)
  : type_arguments(std::move(type_arguments))
{
  std::replace(class_name.begin(), class_name.end(), '.', '$');
  std::replace(class_name.begin(), class_name.end(), '/', '.');
  this->class_name = std::move(class_name);
}

void java_ref_type_signaturet::collect_class_dependencies(
  std::set<irep_idt> &deps) const
{
  deps.insert(class_name);
  for(const std::shared_ptr<java_value_type_signaturet> &type_arg :
      type_arguments)
  {
    type_arg->collect_class_dependencies(deps);
  }
}

typet java_ref_type_signaturet::get_type(
  const std::string &class_name_prefix) const
{
  std::string identifier = "java::" + class_name;
  struct_tag_typet struct_tag_type(identifier);
  struct_tag_type.set(ID_C_base_name, class_name);

  if(type_arguments.empty())
    return java_reference_type(struct_tag_type);

  java_generic_typet result(struct_tag_type);
  std::transform(
    type_arguments.begin(),
    type_arguments.end(),
    std::back_inserter(result.generic_type_arguments()),
    [&class_name_prefix](
      const std::shared_ptr<java_value_type_signaturet> &type_argument)
    {
      const typet type = type_argument->get_type(class_name_prefix);
      const reference_typet *ref_type =
        type_try_dynamic_cast<reference_typet>(type);
      if(ref_type == nullptr)
        throw unsupported_java_class_signature_exceptiont(
          "All generic type arguments should be references");
      return *ref_type;
    });
  return std::move(result);
}

void java_ref_type_signaturet::output(std::ostream &stm) const
{
  stm << class_name;
  if(!type_arguments.empty())
    stm << "<" << type_arguments << ">";
}

std::ostream &operator<<(
  std::ostream &stm,
  const java_generic_type_parameter_listt &parameters)
{
  bool first = true;
  for(const std::shared_ptr<java_generic_type_parametert> &parameter :
      parameters)
  {
    if(!first)
      stm << ", ";
    else
      first = false;
    stm << *parameter;
  }
  return stm;
}


///////////////////////////////////////////////////////////
// java_class_type_signaturet

java_class_type_signaturet::java_class_type_signaturet(
  const std::string &type_string,
  const java_generic_type_parameter_mapt &outer_parameter_map)
{
  parsable_stringt type_str = type_string;
  explicit_type_parameters = parse_type_parameters(type_str);
  type_parameter_map = outer_parameter_map;
  for(const std::shared_ptr<java_generic_type_parametert> &parameter :
      explicit_type_parameters)
  {
    type_parameter_map.emplace(parameter->name, parameter);
  }
  do
    bases.push_back(parse_type(type_str, type_parameter_map));
  while(!type_str.empty());
}

void java_class_type_signaturet::collect_class_dependencies(
  std::set<irep_idt> &deps) const
{
  for(const std::shared_ptr<java_generic_type_parametert> &parameter :
      explicit_type_parameters)
  {
    parameter->collect_class_dependencies_from_declaration(deps);
  }
  for(const std::shared_ptr<java_value_type_signaturet> &base : bases)
    base->collect_class_dependencies(deps);
}

typet java_class_type_signaturet::get_type(
  const std::string &class_name_prefix) const
{
  // TODO: Implement this
  UNREACHABLE;
}

void java_class_type_signaturet::output(std::ostream &stm) const
{
  stm << "class Foo";
  if(!explicit_type_parameters.empty())
  {
    stm << "<";
    bool first = true;
    for(const std::shared_ptr<java_generic_type_parametert> &parameter :
        explicit_type_parameters)
    {
      if(!first)
        stm << ", ";
      else
        first = false;
      parameter->full_output(stm, true);
    }
    stm << ">";
  }
  stm << " extends " << *bases[0];
  if(bases.size() != 1)
  {
    stm << " implements ";
    bool first = true;
    for(std::size_t i = 1; i < bases.size(); ++i)
    {
      if(!first)
        stm << ", ";
      else
        first = false;
      stm << *bases[i];
    }
  }
}


///////////////////////////////////////////////////////////
// java_method_type_signaturet

java_method_type_signaturet::java_method_type_signaturet(
  const std::string &type_string,
  java_generic_type_parameter_mapt class_parameter_map)
{
  parsable_stringt type_str = type_string;
  explicit_type_parameters = parse_type_parameters(type_str);
  type_parameter_map = class_parameter_map;
  for(const std::shared_ptr<java_generic_type_parametert> &parameter :
      explicit_type_parameters)
  {
    type_parameter_map.emplace(parameter->name, parameter);
  }
  type_str.skip('(', "No '(' at start of method signature");
  while(!type_str.try_skip(')'))
    parameters.push_back(parse_type(type_str, type_parameter_map));
  return_type = parse_type(type_str, type_parameter_map);
  if(!type_str.empty())
    throw parse_exceptiont("Extra content after type signature");
}

void java_method_type_signaturet::collect_class_dependencies(
  std::set<irep_idt> &deps) const
{
  for(const std::shared_ptr<java_generic_type_parametert> &parameter :
      explicit_type_parameters)
  {
    parameter->collect_class_dependencies_from_declaration(deps);
  }
  for(const std::shared_ptr<java_value_type_signaturet> &param : parameters)
    param->collect_class_dependencies(deps);
  return_type->collect_class_dependencies(deps);
}

typet java_method_type_signaturet::get_type(
  const std::string &class_name_prefix) const
{
  code_typet::parameterst parameter_types;
  std::transform(
    parameters.begin(),
    parameters.end(),
    std::back_inserter(parameter_types),
    [&class_name_prefix](
      const std::shared_ptr<java_value_type_signaturet> &parameter)
    {
      return code_typet::parametert(parameter->get_type(class_name_prefix));
    });
  return
    java_method_typet
    { std::move(parameter_types), return_type->get_type(class_name_prefix) };
}

void java_method_type_signaturet::output(std::ostream &stm) const
{
  stm << *return_type << " f";
  if(!explicit_type_parameters.empty())
  {
    stm << "<";
    bool first = true;
    for(const std::shared_ptr<java_generic_type_parametert> &parameter :
        explicit_type_parameters)
    {
      if(!first)
        stm << ", ";
      else
        first = false;
      parameter->full_output(stm, true);
    }
    stm << ">";
  }
  stm << "(" << parameters << ")";
}

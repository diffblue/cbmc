/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <iterator>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>

#include "java_types.h"
#include "java_utils.h"

#ifdef DEBUG
#include <iostream>
#endif

std::vector<typet> parse_list_types(
  const std::string src,
  const std::string class_name_prefix,
  const char opening_bracket,
  const char closing_bracket);

typet java_int_type()
{
  return signedbv_typet(32);
}

typet java_void_type()
{
  return void_typet();
}

typet java_long_type()
{
  return signedbv_typet(64);
}

typet java_short_type()
{
  return signedbv_typet(16);
}

typet java_byte_type()
{
  return signedbv_typet(8);
}

typet java_char_type()
{
  return unsignedbv_typet(16);
}

typet java_float_type()
{
  return ieee_float_spect::single_precision().to_type();
}

typet java_double_type()
{
  return ieee_float_spect::double_precision().to_type();
}

typet java_boolean_type()
{
  // The Java standard doesn't really prescribe the width
  // of a boolean. However, JNI suggests that it's 8 bits.
  // http://docs.oracle.com/javase/7/docs/technotes/guides/jni/spec/types.html
  return c_bool_typet(8);
}

reference_typet java_reference_type(const typet &subtype)
{
  return reference_type(subtype);
}

reference_typet java_lang_object_type()
{
  return java_reference_type(struct_tag_typet("java::java.lang.Object"));
}

/// Construct an array pointer type. It is a pointer to a symbol with identifier
/// java::array[]. Its ID_element_type is set to the corresponding primitive
/// type, or void* for arrays of references.
/// \param subtype: Character indicating the type of array
reference_typet java_array_type(const char subtype)
{
  std::string subtype_str;

  switch(subtype)
  {
  case 'b': subtype_str="byte"; break;
  case 'f': subtype_str="float"; break;
  case 'd': subtype_str="double"; break;
  case 'i': subtype_str="int"; break;
  case 'c': subtype_str="char"; break;
  case 's': subtype_str="short"; break;
  case 'z': subtype_str="boolean"; break;
  case 'v': subtype_str="void"; break;
  case 'j': subtype_str="long"; break;
  case 'l': subtype_str="long"; break;
  case 'a': subtype_str="reference"; break;
  default:
#ifdef DEBUG
    std::cout << "Unrecognised subtype str: " << subtype << std::endl;
#endif
    UNREACHABLE;
  }

  irep_idt class_name="array["+subtype_str+"]";

  struct_tag_typet struct_tag_type("java::" + id2string(class_name));
  struct_tag_type.set(ID_C_base_name, class_name);
  struct_tag_type.set(ID_element_type, java_type_from_char(subtype));

  return java_reference_type(struct_tag_type);
}

/// Return a const reference to the element type of a given java array type
/// \param array_symbol: The java array type
const typet &java_array_element_type(const struct_tag_typet &array_symbol)
{
  DATA_INVARIANT(
    is_java_array_tag(array_symbol.get_identifier()),
    "Symbol should have array tag");
  return array_symbol.find_type(ID_element_type);
}

/// Return a non-const reference to the element type of a given java array type
/// \param array_symbol: The java array type
typet &java_array_element_type(struct_tag_typet &array_symbol)
{
  DATA_INVARIANT(
    is_java_array_tag(array_symbol.get_identifier()),
    "Symbol should have array tag");
  return array_symbol.add_type(ID_element_type);
}

/// Checks whether the given type is an array pointer type
bool is_java_array_type(const typet &type)
{
  if(
    !can_cast_type<pointer_typet>(type) ||
    !can_cast_type<struct_tag_typet>(type.subtype()))
  {
    return false;
  }
  const auto &subtype_struct_tag = to_struct_tag_type(type.subtype());
  return is_java_array_tag(subtype_struct_tag.get_identifier());
}

/// Checks whether the given type is a multi-dimensional array pointer type,
/// i.e., a pointer to an array type with element type also being a pointer to
/// an array type.
bool is_multidim_java_array_type(const typet &type)
{
  return is_java_array_type(type) && is_java_array_type(java_array_element_type(
                                       to_struct_tag_type(type.subtype())));
}

/// See above
/// \param tag: Tag of a struct
/// \return True if the given string is a Java array tag, i.e., has a prefix
///   of java::array[
bool is_java_array_tag(const irep_idt& tag)
{
  return has_prefix(id2string(tag), "java::array[");
}

/// Constructs a type indicated by the given character:
/// - i  integer
/// - l  long
/// - s  short
/// - b  byte
/// - c  character
/// - f  float
/// - d  double
/// - z  boolean
/// - a  reference
typet java_type_from_char(char t)
{
  switch(t)
  {
  case 'i': return java_int_type();
  case 'j': return java_long_type();
  case 'l': return java_long_type();
  case 's': return java_short_type();
  case 'b': return java_byte_type();
  case 'c': return java_char_type();
  case 'f': return java_float_type();
  case 'd': return java_double_type();
  case 'z': return java_boolean_type();
  case 'a': return java_reference_type(void_typet());
  default: UNREACHABLE; return nil_typet();
  }
}

/// Java does not support byte/short return types. These are always promoted.
typet java_bytecode_promotion(const typet &type)
{
  if(type==java_boolean_type() ||
     type==java_char_type() ||
     type==java_byte_type() ||
     type==java_short_type())
    return java_int_type();

  return type;
}

/// Java does not support byte/short return types. These are always promoted.
exprt java_bytecode_promotion(const exprt &expr)
{
  typet new_type=java_bytecode_promotion(expr.type());

  if(new_type==expr.type())
    return expr;
  else
    return typecast_exprt(expr, new_type);
}

/// Take a list of generic type arguments and parse them into the generic type.
/// \param [out] generic_type: The existing generic type to add the information
///   to
/// \param type_arguments: The string representing the generic type arguments
///   for a signature. For example `<TT;Ljava/lang/Foo;LList<LInteger;>;>`
///   (including the wrapping angle brackets).
/// \param class_name_prefix: The name of the class to use to prefix any found
///   generic types
void add_generic_type_information(
  java_generic_typet &generic_type,
  const std::string &type_arguments,
  const std::string &class_name_prefix)
{
  PRECONDITION(type_arguments.size() >= 2);
  PRECONDITION(type_arguments[0] == '<');
  PRECONDITION(type_arguments[type_arguments.size() - 1] == '>');

  // Parse contained arguments, can be either type parameters (`TT;`)
  // or instantiated types - either generic types (`LList<LInteger;>;`) or
  // just references (`Ljava/lang/Foo;`)
  std::vector<typet> type_arguments_types =
    parse_list_types(type_arguments, class_name_prefix, '<', '>');

  // We should have at least one generic type argument
  CHECK_RETURN(!type_arguments_types.empty());

  // Add the type arguments to the generic type
  std::transform(
    type_arguments_types.begin(),
    type_arguments_types.end(),
    std::back_inserter(generic_type.generic_type_arguments()),
    [](const typet &type) -> reference_typet
    {
      INVARIANT(
        is_reference(type), "All generic type arguments should be references");
      return to_reference_type(type);
    });
}

/// Take a signature string and remove everything in angle brackets allowing
/// for the type to be parsed normally.
/// \param src: The input string
/// \return The input string with everything between angle brackets removed
std::string erase_type_arguments(const std::string &src)
{
  std::string class_name = src;
  std::size_t f_pos = class_name.find('<', 1);

  while(f_pos != std::string::npos)
  {
    std::size_t e_pos = find_closing_delimiter(class_name, f_pos, '<', '>');
    if(e_pos == std::string::npos)
    {
      throw unsupported_java_class_signature_exceptiont(
        "Failed to find generic signature closing delimiter (or recursive "
        "generic): " +
        src);
    }

    // erase generic information between brackets
    class_name.erase(f_pos, e_pos - f_pos + 1);

    // Search the remainder of the string for generic signature
    f_pos = class_name.find('<', f_pos + 1);
  }
  return class_name;
}

/// Returns the full class name, skipping over the generics.
/// \param src: a type descriptor or signature
///   1. Signature:  Lcom/package/OuterClass<TT;>.Inner;
///   2. Descriptor: Lcom.package.OuterClass$Inner;
/// \return The full name of the class like com.package.OuterClass.Inner (for
///   both examples).
std::string gather_full_class_name(const std::string &src)
{
  PRECONDITION(src.size() >= 2);
  PRECONDITION(src[0] == 'L');
  PRECONDITION(src[src.size() - 1] == ';');

  std::string class_name = src.substr(1, src.size() - 2);

  class_name = erase_type_arguments(class_name);

  std::replace(class_name.begin(), class_name.end(), '.', '$');
  std::replace(class_name.begin(), class_name.end(), '/', '.');
  return class_name;
}

/// Given a substring of a descriptor or signature that contains one or more
/// types parse out the individual types. This is used for parsing the
/// parameters of a function or the generic type variables/parameters or
/// arguments contained within angle brackets.
/// \param src: The input string that is wrapped in either ( ) or < >
/// \param class_name_prefix: The name of the class to use to prefix any found
///   generic types
/// \param opening_bracket: For checking string is passed in as expected, the
///   opening bracket (i.e. '(' or '<').
/// \param closing_bracket: For checking string is passed in as expected, the
///   closing bracket (i.e. ')' or '>').
/// \return A vector of types that the string represents
std::vector<typet> parse_list_types(
  const std::string src,
  const std::string class_name_prefix,
  const char opening_bracket,
  const char closing_bracket)
{
  // Loop over the types in the given string, parsing each one in turn
  // and adding to the type_list
  std::vector<typet> type_list;
  for(const std::string &raw_type :
      parse_raw_list_types(src, opening_bracket, closing_bracket))
  {
    const typet new_type = java_type_from_string(raw_type, class_name_prefix);
    INVARIANT(new_type != nil_typet(), "Failed to parse type");
    type_list.push_back(new_type);
  }
  return type_list;
}

/// Given a substring of a descriptor or signature that contains one or more
/// types parse out the individual type strings.
/// \param src: The input string that is wrapped in either ( ) or < >
/// \param opening_bracket: For checking string is passed in as expected, the
///   opening bracket (i.e. '(' or '<').
/// \param closing_bracket: For checking string is passed in as expected, the
///   closing bracket (i.e. ')' or '>').
/// \return A vector of strings that represent the bytecode type.
std::vector<std::string> parse_raw_list_types(
  const std::string src,
  const char opening_bracket,
  const char closing_bracket)
{
  PRECONDITION(src.size() >= 2);
  PRECONDITION(src[0] == opening_bracket);
  PRECONDITION(src[src.size() - 1] == closing_bracket);

  // Loop over the types in the given string, parsing each one in turn
  // and adding to the type_list
  std::vector<std::string> type_list;
  for(std::size_t i = 1; i < src.size() - 1; i++)
  {
    size_t start = i;
    while(i < src.size())
    {
      // type is an object type or instantiated generic type
      if(src[i] == 'L')
      {
        i = find_closing_semi_colon_for_reference_type(src, i);
        break;
      }

      // type is an array
      else if(src[i] == '[')
        i++;

      // type is a type variable/parameter
      else if(src[i] == 'T')
        i = src.find(';', i); // ends on ;

      // type is an atomic type (just one character)
      else
      {
        break;
      }
    }

    std::string sub_str = src.substr(start, i - start + 1);
    type_list.emplace_back(sub_str);
  }
  return type_list;
}

/// For parsing a class type reference
/// \param src: The input string
///   Either a signature: "Lpackage/class<TT;>.innerclass<Ljava/lang/Foo;>;
///   Or a descriptor: "Lpackage.class$inner;
/// \param class_name_prefix: The name of the class to use to prefix any found
///   generic types
/// \return The reference type if parsed correctly, no value if parsing fails.
reference_typet
build_class_name(const std::string &src, const std::string &class_name_prefix)
{
  PRECONDITION(src[0] == 'L');

  // All reference types must end on a ;
  PRECONDITION(src[src.size() - 1] == ';');

  std::string container_class = gather_full_class_name(src);
  std::string identifier = "java::" + container_class;
  struct_tag_typet struct_tag_type(identifier);
  struct_tag_type.set(ID_C_base_name, container_class);

  std::size_t f_pos = src.find('<', 1);
  if(f_pos != std::string::npos)
  {
    java_generic_typet result(struct_tag_type);
    // get generic type information
    do
    {
      std::size_t e_pos = find_closing_delimiter(src, f_pos, '<', '>');
      if(e_pos == std::string::npos)
        throw unsupported_java_class_signature_exceptiont(
          "Parsing type with unmatched generic bracket: " + src);

      add_generic_type_information(
        result, src.substr(f_pos, e_pos - f_pos + 1), class_name_prefix);

      // Look for the next generic type info (if it exists)
      f_pos = src.find('<', e_pos + 1);
    } while(f_pos != std::string::npos);
    return std::move(result);
  }

  return java_reference_type(struct_tag_type);
}

/// Finds the closing semi-colon ending a ClassTypeSignature that starts at
/// \p starting_point.
/// \param src: The input string to work on.
/// \param starting_point: The string position where the opening 'L' we want to
///   find the closing ';' for.
/// \return The string position corresponding to the matching ';'. For example:
///   LA;, we would return 2. For LA<TT;>; we would return 7.
///   See unit/java_bytecode/java_util_tests.cpp for more examples.
size_t find_closing_semi_colon_for_reference_type(
  const std::string src,
  size_t starting_point)
{
  PRECONDITION(src[starting_point] == 'L');
  size_t next_semi_colon = src.find(';', starting_point);
  INVARIANT(
    next_semi_colon != std::string::npos,
    "There must be a semi-colon somewhere in the input");
  size_t next_angle_bracket = src.find('<', starting_point);

  while(next_angle_bracket < next_semi_colon)
  {
    size_t end_bracket =
      find_closing_delimiter(src, next_angle_bracket, '<', '>');
    INVARIANT(
      end_bracket != std::string::npos, "Must find matching angle bracket");

    next_semi_colon = src.find(';', end_bracket + 1);
    next_angle_bracket = src.find('<', end_bracket + 1);
  }

  return next_semi_colon;
}

/// Transforms a string representation of a Java type into an internal type
/// representation thereof.
///
/// Example use are object types like "Ljava/lang/Integer;", type
/// variables/parameters like "TE;" which require a non-empty
/// \p class_name_prefix or generic types like "Ljava/util/List<TE;>;"
/// or "Ljava/util/List<Ljava/lang/Integer;>;" also requiring
/// \p class_name_prefix.
///
/// \param src: the string representation as used in the class file
/// \param class_name_prefix: name of class to append to generic type
///   variables/parameters
/// \return internal type representation for GOTO programs
typet java_type_from_string(
  const std::string &src,
  const std::string &class_name_prefix)
{
  if(src.empty())
    return nil_typet();

  // a java type is encoded in different ways
  //  - a method type is encoded as '(...)R' where the parenthesis include the
  //    parameter types and R is the type of the return value
  //  - atomic types are encoded as single characters
  //  - array types are encoded as '[' followed by the type of the array
  //    content
  //  - object types are named with prefix 'L' and suffix ';', e.g.,
  //    Ljava/lang/Object;
  //  - type variables are similar to object types but have the prefix 'T'
  switch(src[0])
  {
  case '<':
    {
      // The method signature can optionally have a collection of formal
      // type parameters (e.g. on generic methods on non-generic classes
      // or generic static methods). For now we skip over this part of the
      // signature and continue parsing the rest of the signature as normal
      // So for example, the following java method:
      // static void <T, U> foo(T t, U u, int x);
      // Would have a signature that looks like:
      // <T:Ljava/lang/Object;U:Ljava/lang/Object;>(TT;TU;I)V
      // So we skip all inside the angle brackets and parse the rest of the
      // string:
      // (TT;TU;I)V
      size_t closing_generic=find_closing_delimiter(src, 0, '<', '>');
      if(closing_generic==std::string::npos)
      {
        throw unsupported_java_class_signature_exceptiont(
          "Failed to find generic signature closing delimiter");
      }

      // If there are any bounds between '<' and '>' then we cannot currently
      // parse them, so we give up. This only happens when parsing the
      // signature, so we'll fall back to the result of parsing the
      // descriptor, which will respect the bounds correctly.
      const size_t colon_pos = src.find(':');
      if(colon_pos != std::string::npos && colon_pos < closing_generic)
      {
        throw unsupported_java_class_signature_exceptiont(
          "Cannot currently parse bounds on generic types");
      }

      const typet &method_type=java_type_from_string(
        src.substr(closing_generic+1, std::string::npos), class_name_prefix);

      // This invariant being violated means that tkiley has not understood
      // part of the signature spec.
      // Only class and method signatures can start with a '<' and classes are
      // handled separately.
      INVARIANT(
        method_type.id()==ID_code,
        "This should correspond to method signatures only");

      return method_type;
    }
  case '(': // function type
    {
      std::size_t e_pos=src.rfind(')');
      if(e_pos==std::string::npos)
        return nil_typet();

      typet return_type = java_type_from_string(
        std::string(src, e_pos + 1, std::string::npos), class_name_prefix);

      std::vector<typet> param_types =
        parse_list_types(src.substr(0, e_pos + 1), class_name_prefix, '(', ')');

      // create parameters for each type
      java_method_typet::parameterst parameters;
      std::transform(
        param_types.begin(),
        param_types.end(),
        std::back_inserter(parameters),
        [](const typet &type) { return java_method_typet::parametert(type); });

      return java_method_typet(std::move(parameters), std::move(return_type));
    }

  case '[': // array type
    {
      // If this is a reference array, we generate a plain array[reference]
      // with void* members, but note the real type in ID_element_type.
      if(src.size()<=1)
        return nil_typet();
      char subtype_letter=src[1];
      const typet subtype=
        java_type_from_string(src.substr(1, std::string::npos),
                              class_name_prefix);
      if(subtype_letter=='L' || // [L denotes a reference array of some sort.
         subtype_letter=='[' || // Array-of-arrays
         subtype_letter=='T')   // Array of generic types
        subtype_letter='A';
      typet tmp=java_array_type(std::tolower(subtype_letter));
      tmp.subtype().set(ID_element_type, subtype);
      return tmp;
    }

  case 'B': return java_byte_type();
  case 'F': return java_float_type();
  case 'D': return java_double_type();
  case 'I': return java_int_type();
  case 'C': return java_char_type();
  case 'S': return java_short_type();
  case 'Z': return java_boolean_type();
  case 'V': return java_void_type();
  case 'J': return java_long_type();
  case 'T':
  {
    // parse name of type variable
    INVARIANT(src[src.size()-1]==';', "Generic type name must end on ';'.");
    PRECONDITION(!class_name_prefix.empty());
    irep_idt type_var_name(class_name_prefix+"::"+src.substr(1, src.size()-2));
    return java_generic_parametert(
      type_var_name,
      to_struct_tag_type(
        java_type_from_string("Ljava/lang/Object;").subtype()));
  }
  case 'L':
    {
      return build_class_name(src, class_name_prefix);
    }
  case '*':
  case '+':
  case '-':
  {
#ifdef DEBUG
    std::cout << class_name_prefix << std::endl;
#endif
    throw unsupported_java_class_signature_exceptiont("wild card generic");
  }
  default:
    return nil_typet();
  }
}

char java_char_from_type(const typet &type)
{
  const irep_idt &id=type.id();

  if(id==ID_signedbv)
  {
    const size_t width=to_signedbv_type(type).get_width();
    if(to_signedbv_type(java_int_type()).get_width()==width)
      return 'i';
    else if(to_signedbv_type(java_long_type()).get_width()==width)
      return 'l';
    else if(to_signedbv_type(java_short_type()).get_width()==width)
      return 's';
    else if(to_signedbv_type(java_byte_type()).get_width()==width)
      return 'b';
  }
  else if(id==ID_unsignedbv)
    return 'c';
  else if(id==ID_floatbv)
  {
    const size_t width(to_floatbv_type(type).get_width());
    if(to_floatbv_type(java_float_type()).get_width()==width)
      return 'f';
    else if(to_floatbv_type(java_double_type()).get_width()==width)
      return 'd';
  }
  else if(id==ID_c_bool)
    return 'z';

  return 'a';
}

/// Converts the content of a generic class type into a vector of Java types,
/// that is each type variable of the class has one entry in the returned
/// vector.
/// This also supports parsing of bounds in the form of `<T:CBound>` for classes
/// or `<T::IBound>` for interfaces.
///
/// For example for `HashMap<K, V>` a vector with two elements would be returned
///
/// \return vector of java types representing the generic type variables
std::vector<typet> java_generic_type_from_string(
  const std::string &class_name,
  const std::string &src)
{
  /// the class signature is of the form <TX:Bound_X;:BoundZ;TY:Bound_Y;> or of
  /// the form <TX::Bound_X;:BoundZ;TY:Bound_Y;> if Bound_X is an interface
  size_t signature_end = find_closing_delimiter(src, 0, '<', '>');
  INVARIANT(
    src[0]=='<' && signature_end!=std::string::npos,
    "Class signature has unexpected format");
  std::string signature(src.substr(1, signature_end-1));

  if(signature.find(";:")!=std::string::npos)
    throw unsupported_java_class_signature_exceptiont("multiple bounds");

  PRECONDITION(signature[signature.size()-1]==';');

  std::vector<typet> types;
  size_t var_sep=signature.find(';');
  while(var_sep!=std::string::npos)
  {
    size_t bound_sep=signature.find(':');
    INVARIANT(bound_sep!=std::string::npos, "No bound for type variable.");

    // is bound an interface?
    // in this case the separator is '::'
    if(signature[bound_sep + 1] == ':')
    {
      INVARIANT(
        signature[bound_sep + 2] != ':', "Unknown bound for type variable.");
      bound_sep++;
    }

    std::string type_var_name(
      "java::"+class_name+"::"+signature.substr(0, bound_sep));
    std::string bound_type(signature.substr(bound_sep+1, var_sep-bound_sep));

    java_generic_parametert type_var_type(
      type_var_name,
      to_struct_tag_type(
        java_type_from_string(bound_type, class_name).subtype()));

    types.push_back(type_var_type);
    signature=signature.substr(var_sep+1, std::string::npos);
    var_sep=signature.find(';');
  }
  return types;
}

// java/lang/Object -> java.lang.Object
static std::string slash_to_dot(const std::string &src)
{
  std::string result=src;
  for(std::string::iterator it=result.begin(); it!=result.end(); it++)
    if(*it=='/')
      *it='.';
  return result;
}

struct_tag_typet java_classname(const std::string &id)
{
  if(!id.empty() && id[0]=='[')
    return to_struct_tag_type(java_type_from_string(id).subtype());

  std::string class_name=id;

  class_name=slash_to_dot(class_name);
  irep_idt identifier="java::"+class_name;
  struct_tag_typet struct_tag_type(identifier);
  struct_tag_type.set(ID_C_base_name, class_name);

  return struct_tag_type;
}

/// Programmatic documentation of the structure of a Java array (of either
/// primitives or references) type.
/// A Java array is represented in GOTO in the following way:
/// A struct component with a tag like java::array[type] where type is either
/// a primitive like int, or reference.
/// The struct has precisely three components:
/// 1. \@java.lang.Object: of type struct {java.lang.Object} containing the base
///   class data
/// 2. length: of type Java integer - the length of the array
/// 3. data: of type pointer to either pointer to a primitive type, or pointer
///   to pointer to empty (i.e. a void**) pointing to the contents of the array
/// \param type: A type that might represent a Java array
/// \return True if it is a Java array type, false otherwise
bool is_valid_java_array(const struct_typet &type)
{
  bool correct_num_components=type.components().size()==3;
  if(!correct_num_components)
    return false;

  // First component, the base class (Object) data
  const struct_union_typet::componentt base_class_component=
    type.components()[0];

  bool base_component_valid=true;
  base_component_valid&=base_class_component.get_name()=="@java.lang.Object";

  bool length_component_valid=true;
  const struct_union_typet::componentt length_component=
    type.components()[1];
  length_component_valid&=length_component.get_name()=="length";
  length_component_valid&=length_component.type()==java_int_type();

  bool data_component_valid=true;
  const struct_union_typet::componentt data_component=
    type.components()[2];
  data_component_valid&=data_component.get_name()=="data";
  data_component_valid&=data_component.type().id()==ID_pointer;

  return correct_num_components &&
    base_component_valid &&
    length_component_valid &&
    data_component_valid;
}

/// Compares the types, including checking element types if both types are
/// arrays.
/// \param type1: First type to compare
/// \param type2: Second type to compare
/// \return True if the types are equal, including elemnt types if they are
///   both arrays
bool equal_java_types(const typet &type1, const typet &type2)
{
  bool arrays_with_same_element_type = true;
  if(
    type1.id() == ID_pointer && type2.id() == ID_pointer &&
    type1.subtype().id() == ID_struct_tag &&
    type2.subtype().id() == ID_struct_tag)
  {
    const auto &subtype_symbol1 = to_struct_tag_type(type1.subtype());
    const auto &subtype_symbol2 = to_struct_tag_type(type2.subtype());
    if(
      subtype_symbol1.get_identifier() == subtype_symbol2.get_identifier() &&
      is_java_array_tag(subtype_symbol1.get_identifier()))
    {
      const typet &array_element_type1 =
        java_array_element_type(subtype_symbol1);
      const typet &array_element_type2 =
        java_array_element_type(subtype_symbol2);

      arrays_with_same_element_type =
        equal_java_types(array_element_type1, array_element_type2);
    }
  }
  return (type1 == type2 && arrays_with_same_element_type);
}

void get_dependencies_from_generic_parameters_rec(
  const typet &t,
  std::set<irep_idt> &refs)
{
  // Java generic type that holds different types in its type arguments
  if(is_java_generic_type(t))
  {
    for(const auto type_arg : to_java_generic_type(t).generic_type_arguments())
      get_dependencies_from_generic_parameters_rec(type_arg, refs);
  }

  // Java reference type
  else if(t.id() == ID_pointer)
  {
    get_dependencies_from_generic_parameters_rec(t.subtype(), refs);
  }

  // method type with parameters and return value
  else if(t.id() == ID_code)
  {
    const java_method_typet &c = to_java_method_type(t);
    get_dependencies_from_generic_parameters_rec(c.return_type(), refs);
    for(const auto &param : c.parameters())
      get_dependencies_from_generic_parameters_rec(param.type(), refs);
  }

  // struct tag
  else if(t.id() == ID_struct_tag)
  {
    const auto &struct_tag_type = to_struct_tag_type(t);
    const irep_idt class_name(struct_tag_type.get_identifier());
    if(is_java_array_tag(class_name))
    {
      get_dependencies_from_generic_parameters(
        java_array_element_type(struct_tag_type), refs);
    }
    else
      refs.insert(strip_java_namespace_prefix(class_name));
  }
}

/// Collect information about generic type parameters from a given
/// signature. This is used to get information about class dependencies that
/// must be loaded but only appear as generic type argument, not as a field
/// reference.
/// \param signature: the string representation of the signature to analyze
/// \param [out] refs: the set to insert the names of the found dependencies
void get_dependencies_from_generic_parameters(
  const std::string &signature,
  std::set<irep_idt> &refs)
{
  try
  {
    // class signature with bounds
    if(signature[0] == '<')
    {
      const std::vector<typet> types = java_generic_type_from_string(
        erase_type_arguments(signature), signature);

      for(const auto &t : types)
        get_dependencies_from_generic_parameters_rec(t, refs);
    }

    // class signature without bounds and without wildcards
    else if(signature.find('*') == std::string::npos)
    {
      get_dependencies_from_generic_parameters_rec(
        java_type_from_string(signature, erase_type_arguments(signature)),
        refs);
    }
  }
  catch(unsupported_java_class_signature_exceptiont &)
  {
    // skip for now, if we cannot parse it, we cannot detect which additional
    // classes should be loaded as dependencies
  }
}

/// Collect information about generic type parameters from a given type. This is
/// used to get information about class dependencies that must be loaded but
/// only appear as generic type argument, not as a field reference.
/// \param t: the type to analyze
/// \param [out] refs: the set to insert the names of the found dependencies
void get_dependencies_from_generic_parameters(
  const typet &t,
  std::set<irep_idt> &refs)
{
  get_dependencies_from_generic_parameters_rec(t, refs);
}

/// Construct a generic symbol type by extending the symbol type \p type with
/// generic types extracted from the reference \p base_ref.
/// This assumes that the class named \p class_name_prefix extends or implements
/// the class \p type, and that \p base_ref corresponds to a generic class.
/// For instance since HashMap<K,V> extends Map<K,V> we would call
/// `java_generic_struct_tag_typet(struct_tag_typet("Map"),
/// "Ljava/util/Map<TK;TV;>;", "java.util.HashMap")` which generates a symbol
/// type with identifier "Map", and two generic types with identifier
/// "java.util.HashMap::K" and "java.util.HashMap::V" respectively.
java_generic_struct_tag_typet::java_generic_struct_tag_typet(
  const struct_tag_typet &type,
  const std::string &base_ref,
  const std::string &class_name_prefix)
  : struct_tag_typet(type)
{
  set(ID_C_java_generic_symbol, true);
  const typet &base_type = java_type_from_string(base_ref, class_name_prefix);
  PRECONDITION(is_java_generic_type(base_type));
  const java_generic_typet &gen_base_type = to_java_generic_type(base_type);
  INVARIANT(
    type.get_identifier() ==
      to_struct_tag_type(gen_base_type.subtype()).get_identifier(),
    "identifier of " + type.pretty() + "\n and identifier of type " +
      gen_base_type.subtype().pretty() +
      "\ncreated by java_type_from_string for " + base_ref +
      " should be equal");
  generic_types().insert(
    generic_types().end(),
    gen_base_type.generic_type_arguments().begin(),
    gen_base_type.generic_type_arguments().end());
}

/// Check if this symbol has the given generic type. If yes, return its index
/// in the vector of generic types.
/// \param type: The parameter type we are looking for.
/// \return The index of the type in the vector of generic types.
optionalt<size_t> java_generic_struct_tag_typet::generic_type_index(
  const java_generic_parametert &type) const
{
  const auto &type_variable = type.get_name();
  const auto &generics = generic_types();
  for(std::size_t i = 0; i < generics.size(); ++i)
  {
    if(
      is_java_generic_parameter(generics[i]) &&
      to_java_generic_parameter(generics[i]).get_name() == type_variable)
      return i;
  }
  return {};
}

std::string pretty_java_type(const typet &type)
{
  if(type == java_void_type())
    return "void";
  if(type == java_int_type())
    return "int";
  else if(type == java_long_type())
    return "long";
  else if(type == java_short_type())
    return "short";
  else if(type == java_byte_type())
    return "byte";
  else if(type == java_char_type())
    return "char";
  else if(type == java_float_type())
    return "float";
  else if(type == java_double_type())
    return "double";
  else if(type == java_boolean_type())
    return "boolean";
  else if(type == java_byte_type())
    return "byte";
  else if(is_reference(type))
  {
    if(type.subtype().id() == ID_struct_tag)
    {
      const auto &struct_tag_type = to_struct_tag_type(type.subtype());
      const irep_idt &id = struct_tag_type.get_identifier();
      if(is_java_array_tag(id))
        return pretty_java_type(java_array_element_type(struct_tag_type)) +
               "[]";
      else
        return id2string(strip_java_namespace_prefix(id));
    }
    else
      return "?";
  }
  else
    return "?";
}

std::string pretty_signature(const java_method_typet &method_type)
{
  std::ostringstream result;
  result << '(';

  bool first = true;
  for(const auto p : method_type.parameters())
  {
    if(p.get_this())
      continue;

    if(first)
      first = false;
    else
      result << ", ";

    result << pretty_java_type(p.type());
  }

  result << ')';
  return result.str();
}

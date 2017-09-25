/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>

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
  return java_reference_type(symbol_typet("java::java.lang.Object"));
}

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

  symbol_typet symbol_type("java::"+id2string(class_name));
  symbol_type.set(ID_C_base_name, class_name);
  symbol_type.set(ID_C_element_type, java_type_from_char(subtype));

  return java_reference_type(symbol_type);
}

/// See above
/// \par parameters: Struct tag 'tag'
/// \return True if the given struct is a Java array
bool is_java_array_tag(const irep_idt& tag)
{
  return has_prefix(id2string(tag), "java::array[");
}

bool is_reference_type(const char t)
{
  return 'a'==t;
}

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

/// Transforms a string representation of a Java type into an internal type
/// representation thereof.
///
/// Example use are object types like "Ljava/lang/Integer;", type variables like
/// "TE;" which require a non-empty \p class_name or generic types like
/// "Ljava/util/List<T>;" or "Ljava/util/List<Integer>;"
///
/// \param src: the string representation as used in the class file
/// \param class_name: name of class to append to generic type variables
/// \returns internal type representation for GOTO programs
typet java_type_from_string(
  const std::string &src,
  const std::string &class_name)
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
  case '(': // function type
    {
      std::size_t e_pos=src.rfind(')');
      if(e_pos==std::string::npos)
        return nil_typet();

      code_typet result;

      result.return_type()=
        java_type_from_string(
          std::string(src, e_pos+1, std::string::npos),
          class_name);

      for(std::size_t i=1; i<src.size() && src[i]!=')'; i++)
      {
        code_typet::parametert param;

        size_t start=i;

        while(i<src.size())
        {
          // parameter is an object type or instantiated generic type
          if(src[i]=='L')
          {
            size_t generic_open=src.find('<', i);
            size_t end_pos=src.find(';', i);
            // generic signature
            if(generic_open!=std::string::npos && generic_open<end_pos)
              // point to ';' immediately after the closing '>'
              i=find_closing_delimiter(src, generic_open, '<', '>')+1;
            else
              i=src.find(';', i); // ends on ;
            break;
          }

          // parameter is an array
          else if(src[i]=='[')
            i++;

          // parameter is a type variable
          else if(src[i]=='T')
            i=src.find(';', i); // ends on ;

          // type is an atomic type (just one character)
          else
            break;
        }

        std::string sub_str=src.substr(start, i-start+1);
        param.type()=java_type_from_string(sub_str, class_name);

        if(param.type().id()==ID_symbol)
          param.type()=java_reference_type(param.type());

        result.parameters().push_back(param);
      }

      return result;
    }

  case '[': // array type
    {
      // If this is a reference array, we generate a plain array[reference]
      // with void* members, but note the real type in ID_C_element_type.
      if(src.size()<=1)
        return nil_typet();
      char subtype_letter=src[1];
      const typet subtype=
        java_type_from_string(src.substr(1, std::string::npos), class_name);
      if(subtype_letter=='L' || // [L denotes a reference array of some sort.
         subtype_letter=='[' || // Array-of-arrays
         subtype_letter=='T')   // Array of generic types
        subtype_letter='A';
      typet tmp=java_array_type(std::tolower(subtype_letter));
      tmp.subtype().set(ID_C_element_type, subtype);
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
    PRECONDITION(!class_name.empty());
    irep_idt type_var_name(class_name+"::"+src.substr(1, src.size()-2));
    return java_generic_parametert(
      type_var_name,
      java_type_from_string("Ljava/lang/Object;").subtype());
  }
  case 'L':
    {
      // ends on ;
      if(src[src.size()-1]!=';')
        return nil_typet();
      std::string class_name=src.substr(1, src.size()-2);

      std::size_t f_pos=src.find('<', 1);
      // get generic type information
      if(f_pos!=std::string::npos)
      {
        std::size_t e_pos=find_closing_delimiter(src, f_pos, '<', '>');
        if(e_pos==std::string::npos)
          return nil_typet();

        // construct container type
        std::string generic_container_class=src.substr(1, f_pos-1);

        for(unsigned i=0; i<generic_container_class.size(); i++)
        {
          if(generic_container_class[i]=='/')
            generic_container_class[i]='.';
        }

        java_generic_typet result(
          symbol_typet("java::"+generic_container_class));

#ifdef DEBUG
        std::cout << "INFO: found generic type "
                  << src.substr(f_pos+1, e_pos-f_pos-1)
                  << " in " << src
                  << " with container " << generic_container_class << "\n";
#endif

        // parse contained types, can be either type variables, starting with T
        // or instantiated types
        size_t curr_start=f_pos+1;
        size_t curr_end;
        do
        {
          // find next end of type name
          curr_end=src.find(';', curr_start);
          INVARIANT(
            curr_end!=std::string::npos,
            "Type not terminated with \';\'");
          const size_t end=curr_end-curr_start+1;
          const typet &t=
            java_type_from_string(src.substr(curr_start, end), class_name);
#ifdef DEBUG
          std::cout << "INFO: getting type "
                    << src.substr(curr_start, end) << "\n"
                    << "INFO: type id " << id2string(t.id()) << "\n"
                    << "curr_start " << curr_start
                    << " curr_end " << curr_end
                    << " e_pos " << e_pos
                    << " src " << src << "\n";
#endif
          // is an uninstantiated (pure) generic type
          if(is_java_generic_parameter(t))
          {
            const java_generic_parametert &gen_type=
              to_java_generic_parameter(t);
#ifdef DEBUG
            std::cout << " generic type var " << gen_type.id() << " bound "
                      << to_symbol_type(gen_type.subtype()).get_identifier()
                      << "\n";
#endif
            result.generic_type_variables().push_back(gen_type);
          }

          /// TODO(mgudemann): implement / test the case of iterated generic
          /// types

          // is a concrete type, i.e., instantiation of a generic type of the
          // current type
          else
          {
            java_generic_inst_parametert inst_type(t.subtype());
#ifdef DEBUG
            std::cout << " instantiation of generic type var "
                      << to_symbol_type(t.subtype()).get_identifier() << "\n";
#endif
            result.generic_type_variables().push_back(inst_type);
          }

          curr_start=curr_end+1;
        }
        while(curr_start<e_pos);


        return result;
      }
      for(auto &letter : class_name)
        if(letter=='/')
          letter='.';

      std::string identifier="java::"+class_name;
      symbol_typet symbol_type(identifier);
      symbol_type.set(ID_C_base_name, class_name);

      return java_reference_type(symbol_type);
    }
  case '*':
  {
#ifdef DEBUG
    std::cout << class_name << std::endl;
#endif
    // parse name of type variable
    INVARIANT(src[src.size()-1]==';', "Generic type name must end on ';'.");
    PRECONDITION(!class_name.empty());
//    INVARIANT(
//      src.substr(1, src.size()-2)=="*",
//      "Wildcard types do not have a name");
    irep_idt type_var_name(class_name+"::*");
    return java_generic_parametert(
      type_var_name,
      java_type_from_string("Ljava/lang/Object;").subtype());
  }
  case '+':
  {
#ifdef DEBUG
    std::cout << class_name << std::endl;
#endif
    // parse name of type variable
    INVARIANT(src[src.size()-1]==';', "Generic type name must end on ';'.");
    PRECONDITION(!class_name.empty());
//    INVARIANT(
//      src.substr(1, src.size()-2)=="*",
//      "Wildcard types do not have a name");
    irep_idt type_var_name(class_name+"::*");
    return java_generic_parametert(
      type_var_name,
      java_type_from_string("Ljava/lang/Object;").subtype());
  }
  case '-':
  {
#ifdef DEBUG
    std::cout << class_name << std::endl;
#endif
    // parse name of type variable
    INVARIANT(src[src.size()-1]==';', "Generic type name must end on ';'.");
    PRECONDITION(!class_name.empty());
//    INVARIANT(
//      src.substr(1, src.size()-2)=="*",
//      "Wildcard types do not have a name");
    irep_idt type_var_name(class_name+"::*");
    return java_generic_parametert(
      type_var_name,
      java_type_from_string("Ljava/lang/Object;").subtype());
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
///
/// For example for `HashMap<K, V>` a vector with two elements would be returned
///
/// \returns vector of java types representing the generic type variables
std::vector<typet> java_generic_type_from_string(
  const std::string &class_name,
  const std::string &src)
{
  /// the class signature is of the form <TX:Bound_X;TY:Bound_Y;>base_class
  size_t signature_end=find_closing_delimiter(src, 0, '<', '>');
  INVARIANT(
    src[0]=='<' && signature_end!=std::string::npos,
    "Class signature has unexpected format");
  std::string signature(src.substr(1, signature_end-1));

  PRECONDITION(signature[signature.size()-1]==';');

  std::vector<typet> types;
  size_t var_sep=signature.rfind(';');
  while(var_sep!=std::string::npos)
  {
    size_t bound_sep=signature.find(':');
    INVARIANT(bound_sep!=std::string::npos, "No bound for type variable.");
    std::string type_var_name(
      "java::"+class_name+"::"+signature.substr(0, bound_sep));
    std::string bound_type(signature.substr(bound_sep+1, var_sep-bound_sep));

    java_generic_parametert type_var_type(
      type_var_name,
      java_type_from_string(bound_type, class_name).subtype());

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

symbol_typet java_classname(const std::string &id)
{
  if(!id.empty() && id[0]=='[')
    return to_symbol_type(java_type_from_string(id).subtype());

  std::string class_name=id;

  class_name=slash_to_dot(class_name);
  irep_idt identifier="java::"+class_name;
  symbol_typet symbol_type(identifier);
  symbol_type.set(ID_C_base_name, class_name);

  return symbol_type;
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

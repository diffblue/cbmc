/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_types.h"

#include <cassert>
#include <cctype>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/ieee_float.h>

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
  return to_reference_type(reference_type(subtype));
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
  default: assert(false);
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
  return 'a' == t;
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
  default: assert(false); return nil_typet();
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

typet java_type_from_string(const std::string &src)
{
  if(src.empty())
    return nil_typet();

  switch(src[0])
  {
  case '(': // function type
    {
      std::size_t e_pos=src.rfind(')');
      if(e_pos==std::string::npos)
        return nil_typet();

      code_typet result;

      result.return_type()=
        java_type_from_string(std::string(src, e_pos+1, std::string::npos));

      for(std::size_t i=1; i<src.size() && src[i]!=')'; i++)
      {
        code_typet::parametert param;

        size_t start=i;

        while(i<src.size())
        {
          if(src[i]=='L')
          {
            i=src.find(';', i); // ends on ;
            break;
          }
          else if(src[i]=='[')
            i++;
          else
            break;
        }

        std::string sub_str=src.substr(start, i-start+1);
        param.type()=java_type_from_string(sub_str);

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
        java_type_from_string(src.substr(1, std::string::npos));
      if(subtype_letter=='L' || // [L denotes a reference array of some sort.
         subtype_letter=='[')   // Array-of-arrays
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

  case 'L':
    {
      // ends on ;
      if(src[src.size()-1]!=';')
        return nil_typet();
      std::string class_name=src.substr(1, src.size()-2);

      for(unsigned i=0; i<class_name.size(); i++)
        if(class_name[i]=='/')
          class_name[i]='.';

      std::string identifier="java::"+class_name;

      reference_typet result;
      result.subtype()=symbol_typet(identifier);
      result.subtype().set(ID_C_base_name, class_name);
      return result;
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

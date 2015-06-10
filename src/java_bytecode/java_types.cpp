/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/ieee_float.h>

#include "java_types.h"

/*******************************************************************\

Function: java_int_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_int_type()
{
  return signedbv_typet(32);
}

/*******************************************************************\

Function: java_void_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_void_type()
{
  return void_typet();
}

/*******************************************************************\

Function: java_long_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_long_type()
{
  return signedbv_typet(64);
}

/*******************************************************************\

Function: java_short_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_short_type()
{
  return signedbv_typet(16);
}

/*******************************************************************\

Function: java_byte_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_byte_type()
{
  return signedbv_typet(8);
}

/*******************************************************************\

Function: java_char_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_char_type()
{
  return unsignedbv_typet(16);
}

/*******************************************************************\

Function: java_float_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_float_type()
{
  return ieee_float_spect::single_precision().to_type();
}

/*******************************************************************\

Function: java_double_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_double_type()
{
  return ieee_float_spect::double_precision().to_type();
}

/*******************************************************************\

Function: java_boolean_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_boolean_type()
{
  return c_bool_typet(8);
}

/*******************************************************************\

Function: java_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_reference_type(const typet &subtype)
{
  return reference_typet(subtype);
}

/*******************************************************************\

Function: java_array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

pointer_typet java_array_type(const typet &subtype, unsigned dimension)
{
  assert(dimension!=0);

  // Multi-dimensional arrays in Java are arrays of arrays
  typet final_subtype;
  
  struct_typet array_type;
  
  if(dimension==1)
  {
    final_subtype=subtype;
  
    if(subtype==java_char_type())
      array_type.set_tag("java_char_array");
    else if(subtype==java_float_type())
      array_type.set_tag("java_float_array");
    else if(subtype==java_double_type())
      array_type.set_tag("java_double_array");
    else if(subtype==java_byte_type())
      array_type.set_tag("java_byte_array");
    else if(subtype==java_short_type())
      array_type.set_tag("java_short_array");
    else if(subtype==java_int_type())
      array_type.set_tag("java_int_array");
    else if(subtype==java_long_type())
      array_type.set_tag("java_long_array");
  }
  else
  {
    final_subtype=java_array_type(subtype, dimension-1);
  }

  // This is a pointer to a struct containing the length
  // plus a pointer to the data.

  struct_typet::componentt length("length", java_int_type());
  struct_typet::componentt data("data", pointer_typet(final_subtype));

  array_type.components().push_back(length);
  array_type.components().push_back(data);

  return pointer_typet(array_type);
}

/*******************************************************************\

Function: java_array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

pointer_typet java_array_type(const char subtype)
{
  // This is a pointer to a struct containing the length
  // plus a pointer to the data.

  struct_typet array_type;
  
  if(subtype=='c')
    array_type.set_tag("java_char_array");
  else if(subtype=='f')
    array_type.set_tag("java_float_array");
  else if(subtype=='d')
    array_type.set_tag("java_double_array");
  else if(subtype=='b')
    array_type.set_tag("java_byte_array");
  else if(subtype=='s')
    array_type.set_tag("java_short_array");
  else if(subtype=='i')
    array_type.set_tag("java_int_array");
  else if(subtype=='l')
    array_type.set_tag("java_long_array");

  struct_typet::componentt length("length", java_int_type());
  struct_typet::componentt data("data", pointer_typet(java_type_from_char(subtype)));

  array_type.components().push_back(length);
  array_type.components().push_back(data);

  return pointer_typet(array_type);
}

/*******************************************************************\

Function: is_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_reference_type(const char t)
{
  return 'a' == t;
}

/*******************************************************************\

Function: java_type_from_char

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_type_from_char(char t)
{
  switch(t)
  {
  case 'i': return java_int_type();
  case 'l': return java_long_type();
  case 's': return java_short_type();
  case 'b': return java_byte_type();
  case 'c': return java_char_type();
  case 'f': return java_float_type();
  case 'd': return java_double_type();
  case 'z': return java_boolean_type();
  case 'a': return java_reference_type(void_typet());
  default: assert(false);
  }
}

/*******************************************************************\

Function: java_bytecode_promotion

  Inputs:

 Outputs:

 Purpose: Java does not support byte/short return types.
          These are always promoted.

\*******************************************************************/

typet java_bytecode_promotion(const typet &type)
{
  if(type==java_boolean_type() ||
     type==java_char_type() ||
     type==java_byte_type() ||
     type==java_short_type())
    return java_int_type();

  return type;
}

/*******************************************************************\

Function: java_bytecode_promotion

  Inputs:

 Outputs:

 Purpose: Java does not support byte/short return types.
          These are always promoted.

\*******************************************************************/

exprt java_bytecode_promotion(const exprt &expr)
{
  typet new_type=java_bytecode_promotion(expr.type());

  if(new_type==expr.type())
    return expr;
  else
    return typecast_exprt(expr, new_type);
}

/*******************************************************************\

Function: java_type_from_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_type_from_string(const std::string &src)
{
  if(src.empty())
    return nil_typet();

  switch(src[0])
  {
  case '(': // function type
    {
      std::size_t e_pos=src.rfind(')');
      if(e_pos==std::string::npos) return nil_typet();

      code_typet result;

      // return types are promoted
      result.return_type()=
        java_bytecode_promotion(
          java_type_from_string(std::string(src, e_pos+1, std::string::npos)));

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
      if(src.size()<=2) return nil_typet();
      const typet subtype=java_type_from_string(src.substr(1, std::string::npos));
      return java_array_type(subtype, 1);
    }
    
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
      if(src[src.size()-1]!=';') return nil_typet();
      std::string identifier="java::"+src.substr(1, src.size()-2);

      for(unsigned i=0; i<identifier.size(); i++)
        if(identifier[i]=='/') identifier[i]='.';

      reference_typet result;
      result.subtype()=symbol_typet(identifier);

      return result;
    }
  
  default:
    return nil_typet();
  }
}

/*******************************************************************\

Function: java_char_from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

char java_char_from_type(const typet &type)
{
  const irep_idt &id(type.id());
  if (ID_signedbv == id)
  {
    const unsigned int width(type.get_unsigned_int(ID_width));
    if(java_int_type().get_unsigned_int(ID_width) == width)
      return 'i';
    else if(java_long_type().get_unsigned_int(ID_width) == width)
      return 'l';
    else if(java_short_type().get_unsigned_int(ID_width) == width)
      return 's';
    else if(java_byte_type().get_unsigned_int(ID_width) == width)
      return 'b';
  }
  else if(ID_unsignedbv == id)
    return 'c';
  else if(ID_floatbv == id)
  {
    const unsigned int width(type.get_unsigned_int(ID_width));
    if(java_float_type().get_unsigned_int(ID_width) == width)
      return 'f';
    else if(java_double_type().get_unsigned_int(ID_width) == width)
      return 'd';
  }
  else if(ID_bool == id)
    return 'z';

  return 'a';
}

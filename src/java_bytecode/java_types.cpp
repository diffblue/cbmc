/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/std_types.h>
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
  return bool_typet();
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

typet java_array_type(const typet &subtype)
{
  // array types are proper object types in Java,
  // inheriting from java.lang.Object
  
  class_typet result;
  
  class_typet::componentt length;
  length.set_name("length");
  length.type()=java_int_type(); // the length is 'int'

  result.components().push_back(length);
  
  return result;
}

/*******************************************************************\

Function: java_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_type(char t)
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
      if(src.size()<=2) return nil_typet();
      typet subtype=java_type_from_string(src.substr(1, std::string::npos));
      return java_reference_type(java_array_type(subtype));
    }
    
  case 'F': return java_float_type();    
  case 'D': return java_double_type();
  case 'I': return java_int_type();
  case 'C': return java_char_type();
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


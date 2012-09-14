/*******************************************************************\

Module: C/C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <unicode.h>

#include "../string_constant.h"
#include "../c_types.h"

#include "unescape_string.h"
#include "convert_string_literal.h"

/*******************************************************************\

Function: convert_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_string_literal(const std::string &src)
{
  assert(src.size()>=2);
  
  if(src[0]=='u' && src[1]=='8')
  {
    assert(src[src.size()-1]=='"');
    assert(src[2]=='"');

    std::basic_string<unsigned int> value;
    unescape_wide_string(std::string(src, 3, src.size()-4), value);
    
    // add trailing zero
    value.push_back(0);
    
    // turn into utf-8
    std::string utf8_value=utf32_to_utf8(value); // TODO
    
    string_constantt result;
    result.set_value(utf8_value);

    return result;
  }
  else if(src[0]=='L' || src[0]=='u' || src[0]=='U')
  {
    assert(src[src.size()-1]=='"');
    assert(src[1]=='"');
    
    std::basic_string<unsigned int> value;
    unescape_wide_string(std::string(src, 2, src.size()-3), value);
    
    // add trailing zero
    value.push_back(0);
    
    // L is wchar_t, u is char16_t, U is char32_t.
    typet subtype;
    
    switch(src[0])
    {
    case 'L': subtype=wchar_t_type(); break;
    case 'u': subtype=char16_t_type(); break;
    case 'U': subtype=char32_t_type(); break;
    default:;
    }

    exprt result=exprt(ID_array);
    result.set(ID_C_string_constant, true);
    result.type()=typet(ID_array);
    result.type().subtype()=subtype;
    result.type().set(ID_size, from_integer(value.size(), index_type()));

    result.operands().resize(value.size());
    for(unsigned i=0; i<value.size(); i++)
      result.operands()[i]=from_integer(value[i], subtype);

    return result;
  }
  else
  {
    assert(src[0]=='"');
    assert(src[src.size()-1]=='"');

    std::string value;
    unescape_string(std::string(src, 1, src.size()-2), value);

    string_constantt result;
    result.set_value(value);

    return result;
  }
}

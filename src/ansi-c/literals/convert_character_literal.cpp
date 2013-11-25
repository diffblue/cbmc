/*******************************************************************\

Module: C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/std_expr.h>

#include <ansi-c/c_types.h>

#include "unescape_string.h"
#include "convert_character_literal.h"

/*******************************************************************\

Function: convert_character_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_character_literal(
  const std::string &src,
  bool force_integer_type)
{
  assert(src.size()>=2);
  
  exprt result;

  if(src[0]=='L' || src[0]=='u' || src[0]=='U')
  {
    assert(src[1]=='\'');
    assert(src[src.size()-1]=='\'');
  
    std::basic_string<unsigned int> value;
    unescape_wide_string(std::string(src, 2, src.size()-3), value);
    
    // L is wchar_t, u is char16_t, U is char32_t
    typet type=wchar_t_type();
    
    if(value.size()==0)
      throw "empty wide character literal";
    else if(value.size()==1)
    {
      result=from_integer(value[0], type);
    }
    else if(value.size()>=2 && value.size()<=4)
    {
      // TODO: need to double-check. GCC seems to say that each
      // character is wchar_t wide.
      mp_integer x=0;

      for(unsigned i=0; i<value.size(); i++)
      {
        mp_integer z=(unsigned char)(value[i]);
        z=z<<((value.size()-i-1)*8);
        x+=z;
      }

      // always wchar_t
      result=from_integer(x, type);
    }
    else
      throw "wide literals with "+i2string(value.size())+
            " characters are not supported";
  }
  else
  {
    assert(src[0]=='\'');
    assert(src[src.size()-1]=='\'');

    std::string value;
    unescape_string(std::string(src, 1, src.size()-2), value);

    if(value.size()==0)
      throw "empty character literal";
    else if(value.size()==1)
    {
      typet type=force_integer_type?signed_int_type():char_type();
      result=from_integer(value[0], type);
    }
    else if(value.size()>=2 && value.size()<=4)
    {
      mp_integer x=0;

      for(unsigned i=0; i<value.size(); i++)
      {
        mp_integer z=(unsigned char)(value[i]);
        z=z<<((value.size()-i-1)*8);
        x+=z;
      }

      // always integer, never char!
      result=from_integer(x, signed_int_type());
    }
    else
      throw "literals with "+i2string(value.size())+
            " characters are not supported";
  }
  
  return result;
}

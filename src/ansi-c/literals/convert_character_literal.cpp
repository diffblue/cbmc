/*******************************************************************\

Module: C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <i2string.h>

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

  if(src[0]=='L')
  {
    assert(src[1]=='\'');
    assert(src[src.size()-1]=='\'');
  
    std::vector<unsigned int> value;
    unescape_wide_string(std::string(src, 2, src.size()-3), value);
    
    if(value.size()==0)
      throw "empty wide character literal";
    else if(value.size()==1)
    {
      typet type=force_integer_type?int_type():wchar_t_type();
      result=from_integer(value[0], type);
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
      typet type=force_integer_type?int_type():char_type();
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
      result=from_integer(x, int_type());
    }
    else
      throw "literals with "+i2string(value.size())+
            " characters are not supported";
  }
  
  return result;
}

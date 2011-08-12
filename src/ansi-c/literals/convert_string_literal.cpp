/*******************************************************************\

Module: C/C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>

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

void convert_string_literal(
  const std::string &src,
  std::string &dest)
{
  dest="";

}

/*******************************************************************\

Function: convert_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_string_literal(const std::string &src)
{
  assert(src.size()>=2);
  
  if(src[0]=='L')
  {
    assert(src[1]=='"');
    assert(src[src.size()-1]=='"');

    std::vector<unsigned int> value;
    unescape_wide_string(std::string(src, 2, src.size()-3), value);
    
    // add trailing zero
    value.push_back(0);

    exprt result=exprt(ID_array);
    result.set(ID_C_string_constant, true);
    result.type()=typet(ID_array);
    result.type().subtype()=wchar_t_type();
    result.type().set(ID_size, from_integer(value.size(), index_type()));

    result.operands().resize(value.size());
    for(unsigned i=0; i<value.size(); i++)
      result.operands()[i]=from_integer(value[i], wchar_t_type());

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

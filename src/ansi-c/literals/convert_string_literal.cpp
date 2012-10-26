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

Function: convert_one_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_one_string_literal(
  const std::string &src,
  std::basic_string<unsigned int> &value)
{
  assert(src.size()>=2);

  if(src[0]=='u' && src[1]=='8')
  {
    assert(src[src.size()-1]=='"');
    assert(src[2]=='"');

    unescape_wide_string(std::string(src, 3, src.size()-4), value);
    
    // turn into utf-8
    std::string utf8_value=utf32_to_utf8(value);

    // pad into wide string
    value.resize(utf8_value.size());
    for(unsigned i=0; i<utf8_value.size(); i++)
      value[i]=utf8_value[i];
  }
  else if(src[0]=='L' || src[0]=='u' || src[0]=='U')
  {
    assert(src[src.size()-1]=='"');
    assert(src[1]=='"');
    
    unescape_wide_string(std::string(src, 2, src.size()-3), value);
  }
  else
  {
    assert(src[0]=='"');
    assert(src[src.size()-1]=='"');

    unescape_wide_string(std::string(src, 1, src.size()-2), value);
  }
}

/*******************************************************************\

Function: convert_string_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_string_literal(const std::string &src)
{
  // note that 'src' could be a concatenation of string literals,
  // e.g., something like "asd" "xyz".
  // GCC allows "asd" L"xyz"!

  std::basic_string<unsigned int> value;
  
  char wide=0;
  
  for(unsigned i=0; i<src.size(); i++)
  {
    char ch=src[i];

    // skip whitespace/newline
    if(ch!='L' && ch!='u' && ch!='U' && ch!='"')
      continue;

    if(ch=='L') wide=ch;
    if((ch=='u' || ch=='U') && i+1<src.size() && src[i+1]=='"') wide=ch;

    // find start of sequence
    unsigned j=i;
    while(j<src.size() && src[j]!='"') j++;

    // find end of sequence, considering escaping
    j++;
    while(j<src.size() && src[j]!='"')
    {
      if(src[j]=='\\')
        j+=2;
      else
        j++;
    }

    if(j<src.size())
    {
      std::string tmp_src=std::string(src, i, j-i+1);
      std::basic_string<unsigned int> tmp_value;
      convert_one_string_literal(tmp_src, tmp_value);
      value.append(tmp_value);
      i=j;
    }
  }
  
  if(wide!=0)
  {   
    // add implicit trailing zero
    value.push_back(0);
    
    // L is wchar_t, u is char16_t, U is char32_t.
    typet subtype;
    
    switch(wide)
    {
    case 'L': subtype=wchar_t_type(); break;
    case 'u': subtype=char16_t_type(); break;
    case 'U': subtype=char32_t_type(); break;
    default: assert(false);
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
    std::string char_value;
    
    char_value.resize(value.size());
    
    for(unsigned i=0; i<value.size(); i++)
    {
      // Loss of data here if value[i]>255.
      // gcc issues a warning in this case.
      char_value[i]=value[i];
    }
    
    string_constantt result;
    result.set_value(char_value);
    
    return result;
  }
}

/*******************************************************************\

Module: C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>

#include <arith_tools.h>
#include <config.h>

#include "convert_integer_literal.h"

/*******************************************************************\

Function: convert_integer_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_integer_literal(
  const std::string &src,
  unsigned base)
{
  bool is_unsigned=false;
  unsigned long_cnt=0;
  unsigned width_suffix=0;
  
  for(unsigned i=0; i<src.size(); i++)
  {
    register char ch=src[i];

    if(ch=='u' || ch=='U')
      is_unsigned=true;
    else if(ch=='l' || ch=='L')
      long_cnt++;
    else if(ch=='i' || ch=='I')
      width_suffix=atoi(src.c_str()+i+1);
  }

  mp_integer value;
  
  if(base==10)
  {
    value=string2integer(src, 10);
  }
  else if(base==8)
  {
    value=string2integer(src, 8);
  }
  else if(base==16)
  {
    std::string without_prefix(src, 2, std::string::npos);
    value=string2integer(without_prefix, 16);
  }
  else
    assert(false);

  if(width_suffix!=0)
  {
    // this is a Microsoft extension
    irep_idt cpp_type;
    
    if(width_suffix<=config.ansi_c.int_width)
      cpp_type=is_unsigned?ID_unsigned_int:ID_signed_int;
    else if(width_suffix<=config.ansi_c.long_int_width)
      cpp_type=is_unsigned?ID_unsigned_long_int:ID_signed_long_int;
    else
      cpp_type=is_unsigned?ID_unsigned_long_long_int:ID_signed_long_long_int;

    typet type=typet(is_unsigned?ID_unsignedbv:ID_signedbv);
    type.set(ID_width, width_suffix);
    type.set(ID_C_cpp_type, cpp_type);

    exprt result=from_integer(value, type);
    result.set(ID_C_cformat, src);
    
    return result;    
  }
    
  mp_integer value_abs=value;

  if(value<0)
    value_abs.negate();

  bool is_hex_or_oct=(base==8) || (base==16);
  
  #define FITS(width, signed) \
    ((signed?!is_unsigned:(is_unsigned || is_hex_or_oct)) && \
    (power(2, signed?width-1:width)>value_abs))

  unsigned width;
  bool is_signed=false;
  irep_idt cpp_type;

  if(FITS(config.ansi_c.int_width, true) && long_cnt==0) // int
  {
    width=config.ansi_c.int_width;
    is_signed=true;
    cpp_type=ID_signed_int;
  }
  else if(FITS(config.ansi_c.int_width, false) && long_cnt==0) // unsigned int
  {
    width=config.ansi_c.int_width;
    is_signed=false;
    cpp_type=ID_unsigned_int;
  }
  else if(FITS(config.ansi_c.long_int_width, true) && long_cnt==1) // long int
  {
    width=config.ansi_c.long_int_width;
    is_signed=true;
    cpp_type=ID_signed_long_int;
  }
  else if(FITS(config.ansi_c.long_int_width, false) && long_cnt==1) // unsigned long int
  {
    width=config.ansi_c.long_int_width;
    is_signed=false;
    cpp_type=ID_unsigned_long_int;
  }
  else if(FITS(config.ansi_c.long_long_int_width, true)) // long long int
  {
    width=config.ansi_c.long_long_int_width;
    is_signed=true;
    cpp_type=ID_signed_long_long_int;
  }
  else if(FITS(config.ansi_c.long_long_int_width, false)) // unsigned long long int
  {
    width=config.ansi_c.long_long_int_width;
    is_signed=false;
    cpp_type=ID_unsigned_long_long_int;
  }
  else
  {
    // Way too large. Should consider issuing a warning.
    width=config.ansi_c.long_long_int_width;

    if(is_unsigned)
    {
      is_signed=false;
      cpp_type=ID_unsigned_long_long_int;
    }
    else
      cpp_type=ID_signed_long_long_int;
  }
  
  typet type=typet(is_signed?ID_signedbv:ID_unsignedbv);

  type.set(ID_width, width);  
  type.set(ID_C_cpp_type, cpp_type);

  exprt result=from_integer(value, type);
  result.set(ID_C_cformat, src);

  return result;
}

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

exprt convert_integer_literal(const std::string &src)
{
  bool is_unsigned=false, is_imaginary=false;
  unsigned long_cnt=0;
  unsigned width_suffix=0;
  unsigned base=10;
  
  for(unsigned i=0; i<src.size(); i++)
  {
    register char ch=src[i];

    if(ch=='u' || ch=='U')
      is_unsigned=true;
    else if(ch=='l' || ch=='L')
      long_cnt++;
    else if(ch=='i' || ch=='I')
    {
      // This can be "i128" in MS mode,
      // and "10i" (imaginary) for GCC
      if(config.ansi_c.mode==configt::ansi_ct::MODE_VISUAL_STUDIO)
        width_suffix=atoi(src.c_str()+i+1);
      else
        is_imaginary=true;
    }
    else if(ch=='j' || ch=='J')
      is_imaginary=true;
  }

  mp_integer value;

  if(src.size()>=2 && src[0]=='0')
  {
    base=8;
    value=string2integer(src, 8);
  }
  else if(src.size()>=2 && src[0]=='0' && src[1]=='1')
  {
    base=16;
    std::string without_prefix(src, 2, std::string::npos);
    value=string2integer(without_prefix, 16);
  }
  else
  {
    // The default is base 10.
    value=string2integer(src, 10);
  }

  if(width_suffix!=0)
  {
    // this is a Microsoft extension
    irep_idt c_type;
    
    if(width_suffix<=config.ansi_c.int_width)
      c_type=is_unsigned?ID_unsigned_int:ID_signed_int;
    else if(width_suffix<=config.ansi_c.long_int_width)
      c_type=is_unsigned?ID_unsigned_long_int:ID_signed_long_int;
    else
      c_type=is_unsigned?ID_unsigned_long_long_int:ID_signed_long_long_int;

    typet type=typet(is_unsigned?ID_unsignedbv:ID_signedbv);
    type.set(ID_width, width_suffix);
    type.set(ID_C_c_type, c_type);

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
  irep_idt c_type;

  if(FITS(config.ansi_c.int_width, true) && long_cnt==0) // int
  {
    width=config.ansi_c.int_width;
    is_signed=true;
    c_type=ID_signed_int;
  }
  else if(FITS(config.ansi_c.int_width, false) && long_cnt==0) // unsigned int
  {
    width=config.ansi_c.int_width;
    is_signed=false;
    c_type=ID_unsigned_int;
  }
  else if(FITS(config.ansi_c.long_int_width, true) && long_cnt!=2) // long int
  {
    width=config.ansi_c.long_int_width;
    is_signed=true;
    c_type=ID_signed_long_int;
  }
  else if(FITS(config.ansi_c.long_int_width, false) && long_cnt!=2) // unsigned long int
  {
    width=config.ansi_c.long_int_width;
    is_signed=false;
    c_type=ID_unsigned_long_int;
  }
  else if(FITS(config.ansi_c.long_long_int_width, true)) // long long int
  {
    width=config.ansi_c.long_long_int_width;
    is_signed=true;
    c_type=ID_signed_long_long_int;
  }
  else if(FITS(config.ansi_c.long_long_int_width, false)) // unsigned long long int
  {
    width=config.ansi_c.long_long_int_width;
    is_signed=false;
    c_type=ID_unsigned_long_long_int;
  }
  else
  {
    // Way too large. Should consider issuing a warning.
    width=config.ansi_c.long_long_int_width;

    if(is_unsigned)
    {
      is_signed=false;
      c_type=ID_unsigned_long_long_int;
    }
    else
      c_type=ID_signed_long_long_int;
  }
  
  typet type=typet(is_signed?ID_signedbv:ID_unsignedbv);

  type.set(ID_width, width);  
  type.set(ID_C_c_type, c_type);

  exprt result=from_integer(value, type);
  result.set(ID_C_cformat, src);

  return result;
}

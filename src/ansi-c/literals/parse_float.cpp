/*******************************************************************\

Module: Conversion of Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Conversion of Expressions

#include "parse_float.h"

#include <algorithm>
#include <cctype>
#include <cstring>

parse_floatt::parse_floatt(const std::string &src)
{
  // {digits}{dot}{digits}{exponent}?{floatsuffix}?
  // {digits}{dot}{exponent}?{floatsuffix}?
  // {dot}{digits}{exponent}?{floatsuffix}?
  // {digits}{exponent}{floatsuffix}?

  // Hex format (C99):
  // 0x{hexdigits}{dot}{hexdigits}[pP]{exponent}{floatsuffix}?
  // 0x{hexdigits}{dot}[pP]{exponent}{floatsuffix}?

  // These are case-insensitive, and we handle this
  // by first converting to lower case.

  std::string src_lower=src;
  std::transform(src_lower.begin(), src_lower.end(),
                 src_lower.begin(), ::tolower);

  const char *p=src_lower.c_str();

  std::string str_whole_number,
              str_fraction_part,
              str_exponent;

  exponent_base=10;

  // is this hex?

  if(src_lower.size()>=2 && src_lower[0]=='0' && src_lower[1]=='x')
  {
    // skip the 0x
    p+=2;

    exponent_base=2;

    // get whole number part
    while(*p!='.' && *p!=0 && *p!='p')
    {
      str_whole_number+=*p;
      p++;
    }

    // skip dot
    if(*p=='.')
      p++;

    // get fraction part
    while(*p!=0 && *p!='p')
    {
      str_fraction_part+=*p;
      p++;
    }

    // skip p
    if(*p=='p')
      p++;

    // skip +
    if(*p=='+')
      p++;

    // get exponent
    while(*p!=0 && *p!='f' && *p!='l' &&
          *p!='w' && *p!='q' && *p!='d')
    {
      str_exponent+=*p;
      p++;
    }

    std::string str_number=str_whole_number+
                           str_fraction_part;

    // The significand part is interpreted as a (decimal or hexadecimal)
    // rational number; the digit sequence in the exponent part is
    // interpreted as a decimal integer.

    if(str_number.empty())
      significand=0;
    else
      significand=string2integer(str_number, 16); // hex

    if(str_exponent.empty())
      exponent=0;
    else
      exponent=string2integer(str_exponent, 10); // decimal

    // adjust exponent
    exponent-=str_fraction_part.size()*4; // each digit has 4 bits
  }
  else
  {
    // get whole number part
    while(*p!='.' && *p!=0 && *p!='e' &&
          *p!='f' && *p!='l' &&
          *p!='w' && *p!='q' && *p!='d' &&
          *p!='i' && *p!='j')
    {
      str_whole_number+=*p;
      p++;
    }

    // skip dot
    if(*p=='.')
      p++;

    // get fraction part
    while(*p!=0 && *p!='e' &&
          *p!='f' && *p!='l' &&
          *p!='w' && *p!='q' && *p!='d' &&
          *p!='i' && *p!='j')
    {
      str_fraction_part+=*p;
      p++;
    }

    // skip e
    if(*p=='e')
      p++;

    // skip +
    if(*p=='+')
      p++;

    // get exponent
    while(*p!=0 && *p!='f' && *p!='l' &&
          *p!='w' && *p!='q' && *p!='d' &&
          *p!='i' && *p!='j')
    {
      str_exponent+=*p;
      p++;
    }

    std::string str_number=str_whole_number+
                           str_fraction_part;

    if(str_number.empty())
      significand=0;
    else
      significand=string2integer(str_number, 10);

    if(str_exponent.empty())
      exponent=0;
    else
      exponent=string2integer(str_exponent, 10);

    // adjust exponent
    exponent-=str_fraction_part.size();
  }

  // get flags
  is_float=is_long=false;
  is_imaginary=is_decimal=false;
  is_float16=false;
  is_float32=is_float32x=false;
  is_float64=is_float64x=false;
  is_float80=false;
  is_float128=is_float128x=false;

  if(strcmp(p, "f16")==0)
    is_float16=true;
  else if(strcmp(p, "f32")==0)
    is_float32=true;
  else if(strcmp(p, "f32x")==0)
    is_float32x=true;
  else if(strcmp(p, "f64")==0)
    is_float64=true;
  else if(strcmp(p, "f64x")==0)
    is_float64x=true;
  else if(strcmp(p, "f128")==0)
    is_float128=true;
  else if(strcmp(p, "f128x")==0)
    is_float128x=true;
  else
  {
    while(*p!=0)
    {
      if(*p=='f')
        is_float=true;
      else if(*p=='l')
        is_long=true;
      else if(*p=='i' || *p=='j')
        is_imaginary=true;
      // http://gcc.gnu.org/onlinedocs/gcc/Decimal-Float.html
      else if(*p=='d')
        // a suffix with just d or D but nothing else is a GCC extension with no
        // particular effect -- and forbidden by Clang
        is_decimal=is_decimal || *(p+1)!=0;
      // http://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
      else if(*p=='w')
        is_float80=true;
      else if(*p=='q')
        is_float128=true;

      p++;
    }
  }
}

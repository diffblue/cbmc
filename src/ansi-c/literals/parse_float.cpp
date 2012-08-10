/*******************************************************************\

Module: Conversion of Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>

#include "parse_float.h"

/*******************************************************************\

Function: convert_ct::parse_float

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_float(
  const std::string &src,
  mp_integer &significand,
  mp_integer &exponent,
  unsigned &exponent_base,
  bool &is_float, bool &is_long, bool &is_imaginary)
{
  // {digits}{dot}{digits}{exponent}?{floatsuffix}?
  // {digits}{dot}{exponent}?{floatsuffix}?
  // {dot}{digits}{exponent}?{floatsuffix}?
  // {digits}{exponent}{floatsuffix}?

  // Hex format (C99):
  // 0x{hexdigits}{dot}{hexdigits}[pP]{exponent}{floatsuffix}?
  // 0x{hexdigits}{dot}[pP]{exponent}{floatsuffix}?

  const char *p=src.c_str();

  std::string str_whole_number,
              str_fraction_part,
              str_exponent;
              
  exponent_base=10;
  
  // is this hex?
  
  if(src.size()>=2 && src[0]=='0' && tolower(src[1])=='x')
  {
    // skip the 0x
    p+=2;
  
    exponent_base=2;
  
    // get whole number part
    while(*p!='.' && *p!=0 && *p!='p' && *p!='P')
    {
      str_whole_number+=*p;
      p++;
    }

    // skip dot
    if(*p=='.')
      p++;

    // get fraction part
    while(*p!=0 && *p!='p' && *p!='P')
    {
      str_fraction_part+=*p;
      p++;
    }

    // skip P
    if(*p=='p' || *p=='P')
      p++;

    // skip +
    if(*p=='+')
      p++;

    // get exponent
    while(*p!=0 && *p!='f' && *p!='F' && *p!='l' && *p!='L')
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
    while(*p!='.' && *p!=0 && *p!='e' && *p!='E' &&
          *p!='f' && *p!='F' && *p!='l' && *p!='L' &&
          *p!='i' && *p!='I' && *p!='j' && *p!='J')
    {
      str_whole_number+=*p;
      p++;
    }

    // skip dot
    if(*p=='.')
      p++;

    // get fraction part
    while(*p!=0 && *p!='e' && *p!='E' &&
          *p!='f' && *p!='F' && *p!='l' && *p!='L' &&
          *p!='i' && *p!='I' && *p!='j' && *p!='J')
    {
      str_fraction_part+=*p;
      p++;
    }

    // skip E
    if(*p=='e' || *p=='E')
      p++;

    // skip +
    if(*p=='+')
      p++;

    // get exponent
    while(*p!=0 && *p!='f' && *p!='F' && *p!='l' && *p!='L' &&
          *p!='i' && *p!='I' && *p!='j' && *p!='J')
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
  is_float=is_long=is_imaginary=false;

  while(*p!=0)
  {
    if(*p=='f' || *p=='F')
      is_float=true;
    else if(*p=='l' || *p=='L')
      is_long=true;
    else if(*p=='i' || *p=='I' || *p=='j' || *p=='J')
      is_imaginary=true;

    p++;
  }
}

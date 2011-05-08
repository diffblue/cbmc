/*******************************************************************\

Module: Conversion of Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  bool &is_float, bool &is_long)
{
  // <INITIAL>{digits}{dot}{digits}{exponent}?{floatsuffix}?
  // <INITIAL>{digits}{dot}{exponent}?{floatsuffix}?
  // <INITIAL>{dot}{digits}{exponent}?{floatsuffix}?
  // <INITIAL>{digits}{exponent}{floatsuffix}?

  const char *p=src.c_str();

  std::string str_whole_number,
              str_fraction_part,
              str_exponent;

  // get whole number part
  while(*p!='.' && *p!=0 && *p!='e' && *p!='E' &&
        *p!='f' && *p!='F' && *p!='l' && *p!='L')
  {
    str_whole_number+=*p;
    p++;
  }

  // skip dot
  if(*p=='.')
    p++;

  // get fraction part
  while(*p!=0 && *p!='e' && *p!='E' &&
         *p!='f' && *p!='F' && *p!='l' && *p!='L')
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
  while(*p!=0 && *p!='f' && *p!='F' && *p!='l' && *p!='L')
  {
    str_exponent+=*p;
    p++;
  }

  // get flags
  is_float=is_long=false;

  while(*p!=0)
  {
    if(*p=='f' || *p=='F')
      is_float=true;
    else if(*p=='l' || *p=='L')
      is_long=true;

    p++;
  }

  std::string str_number=str_whole_number+
                         str_fraction_part;

  if(str_number.empty())
    significand=0;
  else
    significand=string2integer(str_number);

  if(str_exponent.empty())
    exponent=0;
  else
    exponent=string2integer(str_exponent);

  // adjust exponent
  exponent-=str_fraction_part.size();
}

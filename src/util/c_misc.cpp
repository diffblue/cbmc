/*******************************************************************\

Module: ANSI-C Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdio.h>

#include <c_misc.h>

/*******************************************************************\

Function: MetaChar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void MetaChar(std::string &out, char c, bool inString)
{
  switch (c)
  {
  case '\'':
    if (inString) 
      out+="'";
    else
      out+="\\'";
    break;

  case '"':
    if (inString) 
      out+="\\\"";
    else
      out+="\"";
    break;

  case '\0':
    out+="\\0";
    break;

  case '\\':
    out+="\\\\";
    break;

  case '\n':
    out+="\\n";
    break;

  case '\t':
    out+="\\t";
    break;

  case '\r':
    out+="\\r";
    break;

  case '\f':
    out+="\\f";
    break;

  case '\b':
    out+="\\b";
    break;

  case '\v':
    out+="\\v";
    break;

  case '\a':
    out+="\\a";
    break;

  default:
    // Show low and high ascii as octal
    if ((c < ' ') || (c >= 127))
    {
        char octbuf[8];
        sprintf(octbuf, "%03o", (unsigned char) c);
        out+="\\";
        out+=octbuf;
    }
    else
        out+=c;
    break;
  }
}

/*******************************************************************\

Function: MetaString

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void MetaString(std::string &out, const std::string &in)
{
  for(unsigned i=0; i<in.size(); i++)
    MetaChar(out, in[i], true);
}

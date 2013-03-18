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
  switch(c)
  {
  case '\'':
    if(inString) 
      out+="'";
    else
      out+="\\'";
    break;

  case '"':
    if(inString) 
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
    // Show low and certain high ascii as octal
    if(((unsigned char)c < ' ') || (c == 127))
    {
      char octbuf[8];
      sprintf(octbuf, "%03o", (unsigned char) c);
      out+="\\";
      out+=octbuf;
    }
    else
    {
      // leave everything else to permit UTF-8 and 8-bit codepages
      out+=c;
    }

    break;
  }
}

/*******************************************************************\

Function: MetaChar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string MetaChar(char c)
{
  std::string result;
  MetaChar(result, c, false);
  return result;
}

/*******************************************************************\

Function: MetaString

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string MetaString(const std::string &in)
{
  std::string result;
  
  for(unsigned i=0; i<in.size(); i++)
    MetaChar(result, in[i], true);
  
  return result;
}

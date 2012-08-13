/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cctype>
#include <cstdio>

#include "unescape_string.h"

/*******************************************************************\

Function: unescape_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unescape_string(
  const std::string &src,
  std::string &dest)
{
  dest="";
  dest.reserve(src.size());

  for(unsigned i=0; i<src.size(); i++)
  {
    char ch=src[i];

    if(ch=='\\') // escape?
    {
      i++;
      assert(i<src.size()); // backslash can't be last character
      
      ch=src[i];
      switch(ch)
      {
      case '\\': dest+=ch; break;
      case 'n': dest+='\n'; break; /* NL (0x0a) */
      case 't': dest+='\t'; break; /* HT (0x09) */
      case 'v': dest+='\v'; break; /* VT (0x0b) */
      case 'b': dest+='\b'; break; /* BS (0x08) */
      case 'r': dest+='\r'; break; /* CR (0x0d) */
      case 'f': dest+='\f'; break; /* FF (0x0c) */
      case 'a': dest+='\a'; break; /* BEL (0x07) */
      case '"': dest+='"'; break;
      case '\'': dest+='\''; break;
      
      case 'x': // hex
        i++;

        {
          std::string hex;

          while(i<src.size() && isxdigit(src[i]))
          {
            hex+=src[i];
            i++;
          }
        
          unsigned int result;
          sscanf(hex.c_str(), "%x", &result);
          ch=result;
        }
        
        dest+=ch;
      
        break;
      
      default:
        if(isdigit(ch)) // octal
        {
          std::string octal;
          
          while(i<src.size() && isdigit(src[i]))
          {
            octal+=src[i];
            i++;
          }
          
          unsigned int result;
          sscanf(octal.c_str(), "%o", &result);
          ch=result;
          dest+=ch;
        }
        else
        {
          // Unknown escape sequence.
          // Both GCC and CL turn \% into %.
          dest.push_back(ch);
        }
      }
    }
    else
      dest+=ch;
  }
}

/*******************************************************************\

Function: unescape_wide_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unescape_wide_string(
  const std::string &src,
  std::vector<unsigned int> &dest)
{
  dest.reserve(src.size());

  for(unsigned i=0; i<src.size(); i++)
  {
    unsigned int ch=(unsigned char)src[i];

    if(ch=='\\') // escape?
    {
      i++;
      assert(i<src.size()); // backslash can't be last character

      ch=(unsigned char)src[i];
      switch(ch)
      {
      case '\\': dest.push_back(ch); break;
      case 'n': dest.push_back('\n'); break; /* NL (0x0a) */
      case 't': dest.push_back('\t'); break; /* HT (0x09) */
      case 'v': dest.push_back('\v'); break; /* VT (0x0b) */
      case 'b': dest.push_back('\b'); break; /* BS (0x08) */
      case 'r': dest.push_back('\r'); break; /* CR (0x0d) */
      case 'f': dest.push_back('\f'); break; /* FF (0x0c) */
      case 'a': dest.push_back('\a'); break; /* BEL (0x07) */
      case '"': dest.push_back('"'); break;
      case '\'': dest.push_back('\''); break;
      
      case 'x': // hex
        i++;

        {
          std::string hex;
          while(i<src.size() && isxdigit(src[i]))
          {
            hex+=src[i];
            i++;
          }
        
          unsigned int result;
          sscanf(hex.c_str(), "%x", &result);
          ch=result;
        }
        
        dest.push_back(ch);      
        break;
      
      default:
        if(isdigit(ch)) // octal
        {
          std::string octal;
          
          while(i<src.size() && isdigit(src[i]))
          {
            octal+=src[i];
            i++;
          }
          
          unsigned int result;
          sscanf(octal.c_str(), "%o", &result);
          ch=result;
          dest.push_back(ch);
        }
        else
        {
          // Unknown escape sequence.
          // Both GCC and CL turn \% into %.
          dest.push_back(ch);
        }
      }
    }
    else
      dest.push_back(ch);
  }
}

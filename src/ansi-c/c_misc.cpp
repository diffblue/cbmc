/*******************************************************************\

Module: ANSI-C Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Misc Utilities

#include "c_misc.h"

#include <sstream>

static void MetaChar(std::ostringstream &out, char c, bool inString)
{
  switch(c)
  {
  case '\'':
    if(inString)
      out << "'";
    else
      out << "\\'";
    break;

  case '"':
    if(inString)
      out << "\\\"";
    else
      out << "\"";
    break;

  case '\0':
    out << "\\0";
    break;

  case '\\':
    out << "\\\\";
    break;

  case '\n':
    out << "\\n";
    break;

  case '\t':
    out << "\\t";
    break;

  case '\r':
    out << "\\r";
    break;

  case '\f':
    out << "\\f";
    break;

  case '\b':
    out << "\\b";
    break;

  case '\v':
    out << "\\v";
    break;

  case '\a':
    out << "\\a";
    break;

  default:
    // Show low and certain high ascii as octal
    if((static_cast<unsigned char>(c)<' ') || (c==127))
    {
      out << "\\" << std::oct << static_cast<unsigned char>(c);
    }
    else
    {
      // leave everything else to permit UTF-8 and 8-bit codepages
      out << c;
    }

    break;
  }
}

#if 0
static std::string MetaChar(char c)
{
  std::string result;
  MetaChar(result, c, false);
  return result;
}
#endif

std::string MetaString(const std::string &in)
{
  std::ostringstream result;

  for(const auto &ch : in)
    MetaChar(result, ch, true);

  return result.str();
}

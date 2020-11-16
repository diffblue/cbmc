/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Conversion

#include "unescape_string.h"

#include <cctype>

#include <util/invariant.h>
#include <util/unicode.h>

static void append_universal_char(
  unsigned int value,
  std::string &dest)
{
  std::basic_string<unsigned int> value_str(1, value);

  // turn into utf-8
  const std::string utf8_value = utf32_native_endian_to_utf8(value_str);

  dest.append(utf8_value);
}

static void append_universal_char(
  unsigned int value,
  std::basic_string<unsigned int> &dest)
{
  dest.push_back(value);
}

template<typename T>
std::basic_string<T> unescape_string_templ(const std::string &src)
{
  std::basic_string<T> dest;

  dest.reserve(src.size()); // about that long, but may be shorter

  for(unsigned i=0; i<src.size(); i++)
  {
    T ch=(unsigned char)src[i];

    if(ch=='\\') // escape?
    {
      // go to next character
      i++;
      INVARIANT(i < src.size(), "backslash can't be last character");

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

      case 'u': // universal character
      case 'U': // universal character
        i++;

        {
          std::string hex;

          const unsigned digits = (ch == 'u') ? 4u : 8u;
          hex.reserve(digits);

          for(unsigned count=digits;
              count!=0 && i<src.size();
              i++, count--)
            hex+=src[i];

          // go back
          i--;

          unsigned int result=hex_to_unsigned(hex.c_str(), hex.size());

          append_universal_char(result, dest);
        }

        break;

      case 'x': // hex
        i++;

        {
          std::string hex;

          while(i<src.size() && isxdigit(src[i]))
          {
            hex+=src[i];
            i++;
          }

          // go back
          i--;

          ch=hex_to_unsigned(hex.c_str(), hex.size());
        }

        // if T isn't sufficiently wide to hold unsigned values
        // the following might truncate; but then
        // universal characters in non-wide strings don't
        // really work; gcc just issues a warning.
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

          // go back
          i--;

          ch=octal_to_unsigned(octal.c_str(), octal.size());
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

  return dest;
}

std::string unescape_string(const std::string &src)
{
  return unescape_string_templ<char>(src);
}

std::basic_string<unsigned int> unescape_wide_string(
  const std::string &src)
{
  return unescape_string_templ<unsigned int>(src);
}

unsigned hex_to_unsigned(const char *hex, std::size_t digits)
{
  unsigned value=0;

  for(; digits!=0; digits--, hex++)
  {
    char ch=*hex;

    if(ch==0)
      break;

    value<<=4;

    if(isdigit(ch))
      value|=ch-'0';
    else if(isxdigit(ch))
      value|=10+tolower(ch)-'a';
  }

  return value;
}

unsigned octal_to_unsigned(const char *octal, std::size_t digits)
{
  unsigned value=0;

  for(; digits!=0; digits--, octal++)
  {
    char ch=*octal;

    if(ch==0)
      break;

    value<<=3;

    if(isdigit(ch))
      value|=ch-'0';
  }

  return value;
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unicode.h"

#include <cstring>
#include <locale>
#include <iomanip>
#include <sstream>
#include <cstdint>

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <windows.h>
#include <util/pragma_pop.def>
#endif

std::string narrow(const wchar_t *s)
{
  #ifdef _WIN32

  int slength=static_cast<int>(wcslen(s));
  int rlength=
    WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  std::string r;
  r.reserve(wcslen(s));
  while(*s!=0)
  {
    r+=static_cast<char>(*s);
    s++;
  }

  return r;
  #endif
}

std::wstring widen(const char *s)
{
  #ifdef _WIN32

  int slength=static_cast<int>(strlen(s));
  int rlength=
    MultiByteToWideChar(CP_UTF8, 0, s, slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, s, slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  std::wstring r;
  r.reserve(strlen(s));
  while(*s!=0)
  {
    r+=wchar_t(*s);
    s++;
  }

  return r;
  #endif
}

std::string narrow(const std::wstring &s)
{
  #ifdef _WIN32

  int slength=static_cast<int>(s.size());
  int rlength=
    WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  return std::string(s.begin(), s.end());
  #endif
}

std::wstring widen(const std::string &s)
{
  #ifdef _WIN32

  int slength=static_cast<int>(s.size());
  int rlength=
    MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  return std::wstring(s.begin(), s.end());
  #endif
}

/// Appends a unicode character to a utf8-encoded string
/// \par parameters: character to append, string to append to
static void utf8_append_code(unsigned int c, std::string &result)
{
  if(c<=0x7f)
    result+=static_cast<char>(c);
  else if(c<=0x7ff)
  {
    result+=static_cast<char>((c >> 6)   | 0xc0);
    result+=static_cast<char>((c &0x3f) | 0x80);
  }
  else if(c<=0xffff)
  {
    result+=static_cast<char>((c >> 12)         | 0xe0);
    result+=static_cast<char>(((c >> 6) &0x3f) | 0x80);
    result+=static_cast<char>((c &0x3f)        | 0x80);
  }
  else
  {
    result+=static_cast<char>((c >> 18)         | 0xf0);
    result+=static_cast<char>(((c >> 12) &0x3f)| 0x80);
    result+=static_cast<char>(((c >> 6) &0x3f) | 0x80);
    result+=static_cast<char>((c &0x3f)        | 0x80);
  }
}

/// \param s UTF-32 encoded wide string
/// \return utf8-encoded string with the same unicode characters as the input.
std::string
utf32_native_endian_to_utf8(const std::basic_string<unsigned int> &s)
{
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto c : s)
    utf8_append_code(c, result);

  return result;
}

std::vector<std::string> narrow_argv(int argc, const wchar_t **argv_wide)
{
  if(argv_wide==nullptr)
    return std::vector<std::string>();

  std::vector<std::string> argv_narrow;
  argv_narrow.reserve(argc);

  for(int i=0; i!=argc; ++i)
    argv_narrow.push_back(narrow(argv_wide[i]));

  return argv_narrow;
}

static void utf16_append_code(unsigned int code, std::wstring &result)
{
  // we do not treat 0xD800 to 0xDFFF, although
  // they are not valid unicode symbols

  if(code<0xFFFF)
  {
    // code is encoded as one UTF16 character
    result += static_cast<wchar_t>(code);
  }
  else // code is encoded as two UTF16 characters
  {
    // if this is valid unicode, we have
    // code<0x10FFFF
    // but let's not check it programmatically

    // encode the code in UTF16
    code=code-0x10000;
    const uint16_t i1 = static_cast<uint16_t>(((code >> 10) & 0x3ff) | 0xD800);
    result += static_cast<wchar_t>(i1);
    const uint16_t i2 = static_cast<uint16_t>((code & 0x3ff) | 0xDC00);
    result += static_cast<wchar_t>(i2);
  }
}


/// Convert UTF8-encoded string to UTF-16 with architecture-native endianness.
/// \par parameters: String in UTF-8 format
/// \return String in UTF-16 format. The encoding follows the endianness of the
///   architecture iff swap_bytes is true.
std::wstring utf8_to_utf16_native_endian(const std::string &in)
{
    std::wstring result;
    result.reserve(in.size());
    std::string::size_type i=0;
    while(i<in.size())
    {
      unsigned char c=in[i++];
      unsigned int code=0;
      // the ifs that follow find out how many UTF8 characters (1-4) store the
      // next unicode character. This is determined by the few most
      // significant bits.
      if(c<=0x7F)
      {
        // if it's one character, then code is exactly the value
        code=c;
      }
      else if(c<=0xDF && i<in.size())
      { // in other cases, we need to read the right number of chars and decode
        // note: if we wanted to make sure that we capture incorrect strings,
        // we should check that whatever follows first character starts with
        // bits 10.
        code = (c & 0x1Fu) << 6;
        c=in[i++];
        code += c & 0x3Fu;
      }
      else if(c<=0xEF && i+1<in.size())
      {
        code = (c & 0xFu) << 12;
        c=in[i++];
        code += (c & 0x3Fu) << 6;
        c=in[i++];
        code += c & 0x3Fu;
      }
      else if(c<=0xF7 && i+2<in.size())
      {
        code = (c & 0x7u) << 18;
        c=in[i++];
        code += (c & 0x3Fu) << 12;
        c=in[i++];
        code += (c & 0x3Fu) << 6;
        c=in[i++];
        code += c & 0x3Fu;
      }
      else
      {
        // The string is not a valid UTF8 string! Either it has some characters
        // missing from a multi-character unicode symbol, or it has a char with
        // too high value.
        // For now, let's replace the character with a space
        code=32;
      }

      utf16_append_code(code, result);
    }

    return result;
}

/// \param ch: UTF-16 character in architecture-native endianness encoding
/// \param result: stream to receive string in US-ASCII format, with \\uxxxx
///                escapes for other characters
/// \param loc: locale to check for printable characters
static void utf16_native_endian_to_java(
  const wchar_t ch,
  std::ostringstream &result,
  const std::locale &loc)
{
  // \u unicode characters are translated very early by the Java compiler and so
  // \u000a or \u000d would become a newline character in a char constant, which
  // is illegal. Instead use \n or \r.
  if(ch == '\n')
    result << "\\n";
  else if(ch == '\r')
    result << "\\r";
  // \f, \b and \t do not need to be escaped, but this will improve readability
  // of generated tests.
  else if(ch == '\f')
    result << "\\f";
  else if(ch == '\b')
    result << "\\b";
  else if(ch == '\t')
    result << "\\t";
  else if(ch <= 255 && isprint(ch, loc))
  {
    const auto uch = static_cast<unsigned char>(ch);
    // ", \ and ' need to be escaped.
    if(uch == '"' || uch == '\\' || uch == '\'')
      result << '\\';
    result << uch;
  }
  else
  {
    // Format ch as a hexadecimal unicode character padded to four digits with
    // zeros.
    result << "\\u" << std::hex << std::setw(4) << std::setfill('0')
           << static_cast<unsigned int>(ch);
  }
}

/// \param ch: UTF-16 character in architecture-native endianness encoding
/// \return String in US-ASCII format, with \\uxxxx escapes for other characters
std::string utf16_native_endian_to_java(const char16_t ch)
{
  std::ostringstream result;
  const std::locale loc;
  utf16_native_endian_to_java(ch, result, loc);
  return result.str();
}

/// \param in: String in UTF-16 (native endianness) format
/// \return String in US-ASCII format, with \\uxxxx escapes for other characters
std::string utf16_native_endian_to_java(const std::wstring &in)
{
  std::ostringstream result;
  const std::locale loc;
  for(const auto ch : in)
    utf16_native_endian_to_java(ch, result, loc);
  return result.str();
}

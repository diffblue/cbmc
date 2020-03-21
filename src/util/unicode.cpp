/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unicode.h"

#include <codecvt>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <locale>
#include <sstream>

#include "invariant.h"

#ifdef _WIN32
#  include <util/pragma_push.def>
#  ifdef _MSC_VER
#    pragma warning(disable : 4668)
// using #if/#elif on undefined macro
#    pragma warning(disable : 5039)
// pointer or reference to potentially throwing function passed to extern C
#  endif
#  include <util/pragma_pop.def>
#  include <windows.h>
#endif

static void utf8_append_code(unsigned int c, std::string &);

std::string narrow(const wchar_t *s)
{
#ifdef _WIN32

  int slength = static_cast<int>(wcslen(s));
  int rlength =
    WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, slength, &r[0], rlength, NULL, NULL);
  return r;

#else
  return narrow(std::wstring(s));
#endif
}

std::wstring widen(const char *s)
{
#ifdef _WIN32

  int slength = static_cast<int>(strlen(s));
  int rlength = MultiByteToWideChar(CP_UTF8, 0, s, slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, s, slength, &r[0], rlength);
  return r;

#else
  return widen(std::string(s));
#endif
}

std::string narrow(const std::wstring &s)
{
#ifdef _WIN32

  int slength = static_cast<int>(s.size());
  int rlength =
    WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, &s[0], slength, &r[0], rlength, NULL, NULL);
  return r;

#else
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto codepoint : s)
    utf8_append_code(codepoint, result);

  return result;
#endif
}

std::wstring widen(const std::string &s)
{
#ifdef _WIN32

  int slength = static_cast<int>(s.size());
  int rlength = MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, &r[0], rlength);
  return r;

#else
  auto utf32 = utf8_to_utf32(std::string(s));

  std::wstring r;
  r.reserve(utf32.size());
  for(auto codepoint : utf32)
    r += codepoint;
  return r;
#endif
}

/// Appends a unicode character to a utf8-encoded string
/// \par parameters: character to append, string to append to
static void utf8_append_code(unsigned int c, std::string &result)
{
  if(c <= 0x7f)
    result += static_cast<char>(c);
  else if(c <= 0x7ff)
  {
    result += static_cast<char>((c >> 6) | 0xc0);
    result += static_cast<char>((c & 0x3f) | 0x80);
  }
  else if(c <= 0xffff)
  {
    result += static_cast<char>((c >> 12) | 0xe0);
    result += static_cast<char>(((c >> 6) & 0x3f) | 0x80);
    result += static_cast<char>((c & 0x3f) | 0x80);
  }
  else
  {
    result += static_cast<char>((c >> 18) | 0xf0);
    result += static_cast<char>(((c >> 12) & 0x3f) | 0x80);
    result += static_cast<char>(((c >> 6) & 0x3f) | 0x80);
    result += static_cast<char>((c & 0x3f) | 0x80);
  }
}

/// \param s: UTF-32 encoded wide string
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
  if(argv_wide == nullptr)
    return std::vector<std::string>();

  std::vector<std::string> argv_narrow;
  argv_narrow.reserve(argc);

  for(int i = 0; i != argc; ++i)
    argv_narrow.push_back(narrow(argv_wide[i]));

  return argv_narrow;
}

static void utf16_append_code(unsigned int code, std::wstring &result)
{
  // we do not treat 0xD800 to 0xDFFF, although
  // they are not valid unicode symbols

  if(code < 0xFFFF)
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
    code = code - 0x10000;
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

  for(auto codepoint : utf8_to_utf32(in))
    utf16_append_code(codepoint, result);

  return result;
}

/// Convert UTF8-encoded string to UTF-32 with architecture-native endianness.
/// \par parameters: String in UTF-8 format
/// \return String in UTF-32 format.
std::u32string utf8_to_utf32(const std::string &utf8_str)
{
  std::u32string result;
  result.reserve(utf8_str.size());
  std::string::size_type i = 0;
  while(i < utf8_str.size())
  {
    unsigned char c = utf8_str[i++];
    char32_t code = 0;
    // the ifs that follow find out how many UTF8 characters (1-4) store the
    // next unicode character. This is determined by the few most
    // significant bits.
    if(c <= 0x7F)
    {
      // if it's one character, then code is exactly the value
      code = c;
    }
    else if(c <= 0xDF && i < utf8_str.size())
    { // in other cases, we need to read the right number of chars and decode
      // note: if we wanted to make sure that we capture incorrect strings,
      // we should check that whatever follows first character starts with
      // bits 10.
      code = (c & 0x1Fu) << 6;
      c = utf8_str[i++];
      code += c & 0x3Fu;
    }
    else if(c <= 0xEF && i + 1 < utf8_str.size())
    {
      code = (c & 0xFu) << 12;
      c = utf8_str[i++];
      code += (c & 0x3Fu) << 6;
      c = utf8_str[i++];
      code += c & 0x3Fu;
    }
    else if(c <= 0xF7 && i + 2 < utf8_str.size())
    {
      code = (c & 0x7u) << 18;
      c = utf8_str[i++];
      code += (c & 0x3Fu) << 12;
      c = utf8_str[i++];
      code += (c & 0x3Fu) << 6;
      c = utf8_str[i++];
      code += c & 0x3Fu;
    }
    else
    {
      // The string is not a valid UTF8 string! Either it has some characters
      // missing from a multi-character unicode symbol, or it has a char with
      // too high value.
      // For now, let's replace the character with a space
      code = 32;
    }

    result.append(1, code);
  }

  return result;
}

/// Escapes non-printable characters, whitespace except for spaces, double
/// quotes and backslashes. This should yield a valid Java string literal.
/// Note that this specifically does not escape single quotes, as these are not
/// required to be escaped for Java string literals.
/// \param ch: UTF-16 character in architecture-native endianness encoding
/// \param result: stream to receive string in US-ASCII format, with \\uxxxx
///   escapes for other characters
/// \param loc: locale to check for printable characters
static void utf16_native_endian_to_java_string(
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
    // ", and \ need to be escaped, but not ' for java strings
    // e.g. "\"\\" needs escaping but "'" does not.
    if(uch == '"' || uch == '\\')
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

/// Escapes non-printable characters, whitespace except for spaces, double- and
/// single-quotes and backslashes. This should yield a valid Java identifier.
/// \param ch: UTF-16 character in architecture-native endianness encoding
/// \param result: stream to receive string in US-ASCII format, with \\uxxxx
///   escapes for other characters
/// \param loc: locale to check for printable characters
static void utf16_native_endian_to_java(
  const wchar_t ch,
  std::ostringstream &result,
  const std::locale &loc)
{
  if(ch == (wchar_t)'\'')
  {
    const auto uch = static_cast<unsigned char>(ch);
    // ' needs to be escaped for java characters, e.g. '\''
    result << '\\' << uch;
  }
  else
  {
    utf16_native_endian_to_java_string(ch, result, loc);
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

/// Escapes non-printable characters, whitespace except for spaces, double
/// quotes and backslashes. This should yield a valid Java string literal.
/// Note that this specifically does not escape single quotes, as these are not
/// required to be escaped for Java string literals.
/// \param in: String in UTF-16 (native endianness) format
/// \return Valid Java string literal in US-ASCII format, with \\uxxxx escapes
/// for other characters
std::string utf16_native_endian_to_java_string(const std::wstring &in)
{
  std::ostringstream result;
  const std::locale loc;
  for(const auto ch : in)
    utf16_native_endian_to_java_string(ch, result, loc);
  return result.str();
}

std::string utf16_native_endian_to_utf8(const char16_t utf16_char)
{
  return utf16_native_endian_to_utf8(std::u16string(1, utf16_char));
}

std::string utf16_native_endian_to_utf8(const std::u16string &utf16_str)
{
#ifdef _MSC_VER
  // Workaround for Visual Studio bug, see
  // https://stackoverflow.com/questions/32055357
  std::wstring wide_string(utf16_str.begin(), utf16_str.end());
  return std::wstring_convert<std::codecvt_utf8_utf16<wchar_t>, wchar_t>{}
    .to_bytes(wide_string);
#else
  return std::wstring_convert<std::codecvt_utf8_utf16<char16_t>, char16_t>{}
    .to_bytes(utf16_str);
#endif
}

char16_t codepoint_hex_to_utf16_native_endian(const std::string &hex)
{
  PRECONDITION(hex.length() == 4);
  return std::strtol(hex.c_str(), nullptr, 16);
}

std::string codepoint_hex_to_utf8(const std::string &hex)
{
  return utf16_native_endian_to_utf8(codepoint_hex_to_utf16_native_endian(hex));
}

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_UNICODE_H
#define CPROVER_UTIL_UNICODE_H

#include <algorithm>
#include <string>
#include <vector>

// we follow the ideas suggested at
// http://www.utf8everywhere.org/

std::string narrow(const wchar_t *s);
std::wstring widen(const char *s);
std::string narrow(const std::wstring &s);
std::wstring widen(const std::string &s);

std::string
utf32_native_endian_to_utf8(const std::basic_string<unsigned int> &s);

/// \param utf8_str: UTF-8 string
/// \return UTF-32 encoding of the string
std::u32string utf8_to_utf32(const std::string &utf8_str);

std::wstring utf8_to_utf16_native_endian(const std::string &in);
std::string utf16_native_endian_to_java(const char16_t ch);
std::string utf16_native_endian_to_java(const std::wstring &in);
std::string utf16_native_endian_to_java_string(const std::wstring &in);

std::vector<std::string> narrow_argv(int argc, const wchar_t **argv_wide);

/// \param utf16_char: UTF-16 character in architecture-native endianness
///   encoding
/// \return UTF-8 encoding of the same codepoint
std::string utf16_native_endian_to_utf8(char16_t utf16_char);

/// \param utf16_str: UTF-16 string in architecture-native endianness encoding
/// \return UTF-8 encoding of the string
std::string utf16_native_endian_to_utf8(const std::u16string &utf16_str);

/// \param hex: representation of a BMP codepoint as a four-digit string
///   (e.g.\ "0041" for \\u0041)
/// \return encoding of the codepoint as a single UTF-16 character in
///   architecture-native endianness encoding
char16_t codepoint_hex_to_utf16_native_endian(const std::string &hex);

/// \param hex: representation of a BMP codepoint as a four-digit string
///   (e.g.\ "0041" for \\u0041)
/// \return UTF-8 encoding of the codepoint
std::string codepoint_hex_to_utf8(const std::string &hex);

template <typename It>
std::vector<const char *> to_c_str_array(It b, It e)
{
  // Assumes that walking the range will be faster than repeated allocation
  std::vector<const char *> ret(std::distance(b, e) + 1, nullptr);
  std::transform(
    b, e, std::begin(ret), [](const std::string &s) { return s.c_str(); });
  return ret;
}

#endif // CPROVER_UTIL_UNICODE_H

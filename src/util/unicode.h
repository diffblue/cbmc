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

std::string utf32_to_utf8(const std::basic_string<unsigned int> &s);

std::wstring utf8_to_utf16_big_endian(const std::string &);
std::wstring utf8_to_utf16_little_endian(const std::string &);
std::string utf16_little_endian_to_ascii(const std::wstring &in);

std::vector<std::string> narrow_argv(int argc, const wchar_t **argv_wide);

template <typename It>
std::vector<const char *> to_c_str_array(It b, It e)
{
  // Assumes that walking the range will be faster than repeated allocation
  std::vector<const char *> ret(std::distance(b, e) + 1, nullptr);
  std::transform(b, e, std::begin(ret), [] (const std::string & s)
    {
      return s.c_str();
    });
  return ret;
}

#endif // CPROVER_UTIL_UNICODE_H

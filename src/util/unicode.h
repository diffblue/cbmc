/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UNICODE_H
#define CPROVER_UTIL_UNICODE_H

#include <string>

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

const char **narrow_argv(int argc, const wchar_t **argv_wide);

#endif // CPROVER_UTIL_UNICODE_H

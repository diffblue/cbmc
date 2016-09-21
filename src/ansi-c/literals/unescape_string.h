/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_C_TYPECHECK_UNESCAPE_STRING_H
#define CPROVER_C_TYPECHECK_UNESCAPE_STRING_H

#include <string>

std::string unescape_string(const std::string &);
std::basic_string<unsigned int> unescape_wide_string(const std::string &);

unsigned hex_to_unsigned(const char *, unsigned digits);
unsigned octal_to_unsigned(const char *, unsigned digits);

#endif

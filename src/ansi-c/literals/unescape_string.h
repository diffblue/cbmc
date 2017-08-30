/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Conversion

#ifndef CPROVER_ANSI_C_LITERALS_UNESCAPE_STRING_H
#define CPROVER_ANSI_C_LITERALS_UNESCAPE_STRING_H

#include <string>

std::string unescape_string(const std::string &);
std::basic_string<unsigned int> unescape_wide_string(const std::string &);

unsigned hex_to_unsigned(const char *, std::size_t digits);
unsigned octal_to_unsigned(const char *, std::size_t digits);

#endif // CPROVER_ANSI_C_LITERALS_UNESCAPE_STRING_H

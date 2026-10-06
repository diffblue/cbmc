/*******************************************************************\

Module: C/C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C/C++ Language Conversion

#ifndef CPROVER_ANSI_C_LITERALS_CONVERT_STRING_LITERAL_H
#define CPROVER_ANSI_C_LITERALS_CONVERT_STRING_LITERAL_H

#include <string>

#include <util/expr.h>

/// \param src: the literal, possibly a concatenation of string literals
/// \param char8: give a u8 literal type const char8_t[N] (C++20
///   [lex.string]/6) rather than const char[N]
exprt convert_string_literal(const std::string &src, bool char8 = false);

#endif // CPROVER_ANSI_C_LITERALS_CONVERT_STRING_LITERAL_H

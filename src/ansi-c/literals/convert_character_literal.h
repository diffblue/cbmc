/*******************************************************************\

Module: C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Conversion

#ifndef CPROVER_ANSI_C_LITERALS_CONVERT_CHARACTER_LITERAL_H
#define CPROVER_ANSI_C_LITERALS_CONVERT_CHARACTER_LITERAL_H

#include <string>

#include <util/expr.h>

// Ugh. Characters have type 'int' in C, but type
// 'char' in C++.

/// Convert the character literal \p src to an expression.
/// \param src: the literal as written, including its prefix and quotes
/// \param force_integer_type: give it type int (C) rather than char (C++)
/// \param source_location: the literal's location, for diagnostics
/// \param char8: give a u8 literal type char8_t (C++20 [lex.ccon]/3)
/// \return the character constant
exprt convert_character_literal(
  const std::string &src,
  bool force_integer_type,
  const source_locationt &source_location,
  bool char8 = false);

#endif // CPROVER_ANSI_C_LITERALS_CONVERT_CHARACTER_LITERAL_H

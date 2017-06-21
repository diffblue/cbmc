/*******************************************************************\

Module: C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C Language Conversion

#ifndef CPROVER_ANSI_C_LITERALS_CONVERT_FLOAT_LITERAL_H
#define CPROVER_ANSI_C_LITERALS_CONVERT_FLOAT_LITERAL_H

#include <string>

#include <util/expr.h>

exprt convert_float_literal(const std::string &src);

#endif // CPROVER_ANSI_C_LITERALS_CONVERT_FLOAT_LITERAL_H

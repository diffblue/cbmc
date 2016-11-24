/*******************************************************************\

Module: C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_CONVERT_FLOAT_LITERAL_H
#define CPROVER_ANSI_C_CONVERT_FLOAT_LITERAL_H

#include <string>

#include <util/expr.h>

exprt convert_float_literal(const std::string &src);

#endif

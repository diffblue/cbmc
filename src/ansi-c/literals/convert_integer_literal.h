/*******************************************************************\

Module: C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPP_CONVERT_INTEGER_LITERAL_H
#define CPROVER_CPP_CONVERT_INTEGER_LITERAL_H

#include <string>

#include <util/expr.h>

exprt convert_integer_literal(const std::string &src);

#endif

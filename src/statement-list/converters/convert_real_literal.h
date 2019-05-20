/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_REAL_LITERAL_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_REAL_LITERAL_H

#include <string>

#include <util/expr.h>
#include <util/std_types.h>

/// Converts a string into the corresponding 'Real' expression.
/// \param src: String returned by the parser.
/// \return Constant expression representing the real value.
constant_exprt convert_real_literal(const std::string &src);

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_REAL_VALUE_H

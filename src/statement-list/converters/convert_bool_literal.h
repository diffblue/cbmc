/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_BOOL_LITERAL_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_BOOL_LITERAL_H

#include <string>

#include <util/expr.h>
#include <util/std_expr.h>

/// Converts a string into the corresponding 'Bool' expression.
/// \param src: String returned by the parser.
/// \return Constant expression representing the boolean value.
constant_exprt convert_bool_literal(const std::string &src);

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_INT_LITERAL_H

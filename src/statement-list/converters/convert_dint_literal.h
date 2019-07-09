/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_DINT_LITERAL_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_DINT_LITERAL_H

#include <util/expr.h>
#include <util/std_expr.h>

/// Converts a string into the corresponding 'DInt' expression.
/// \param src: String returned by the parser (base 10).
/// \return Constant expression representing the double integer value.
constant_exprt convert_dint_dec_literal_value(const std::string &src);

/// Converts a string into the corresponding 'DInt' expression.
/// \param src: String returned by the parser (base 16).
/// \return Constant expression representing the double integer value.
constant_exprt convert_dint_hex_literal_value(const std::string &src);

/// Converts a string into the corresponding 'DInt' expression.
/// \param src: String returned by the parser (base 2).
/// \return Constant expression representing the double integer value.
constant_exprt convert_dint_bit_literal_value(const std::string &src);

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_DNT_LITERAL_H

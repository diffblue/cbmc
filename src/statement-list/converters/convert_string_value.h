/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_STRING_VALUE_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_STRING_VALUE_H

#include <util/std_code.h>
#include <util/string_constant.h>

/// Converts a string into a Statement List identifier.
/// \param src: String returned by the parser.
/// \return Constant string expression representing the identifier.
string_constantt convert_identifier(const std::string &src);

/// Converts a string into a Statement List title.
/// \param src: String returned by the parser.
/// \return Constant string expression representing the title.
string_constantt convert_title(const std::string &src);

/// Converts a string into a Statement List version.
/// \param src: String returned by the parser.
/// \return Constant string expression representing the version.
string_constantt convert_version(const std::string &src);

/// Converts a string into a Statement List label.
/// \param src: String returned by the parser.
/// \return Code label expression representing the label.
code_labelt convert_label(const std::string &src);

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_CONVERT_STRING_VALUE_H

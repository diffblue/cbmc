/*******************************************************************\

Module: Size limit to choose between variable- and fixed-size char arrays

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
///  Size limit to choose between variable- and fixed-size char arrays

#ifndef CPROVER_SOLVERS_STRINGS_MAX_CONCRETE_CHAR_ARRAY_H
#define CPROVER_SOLVERS_STRINGS_MAX_CONCRETE_CHAR_ARRAY_H

#include <cstddef>
#include <util/optional.h>
#include <util/std_types.h>

extern const std::size_t max_concrete_char_array_length;

/// Create a char array type suitable for a variable-length string of
/// perhaps-limited size. This may have a constant- or variable-length type,
/// depending on the size limit given. If no limit is given it will certainly
/// have variable-length type.
/// \param element_type character type
/// \param index_type type for the array size, must match the type of indices
///   this array
/// \param max_length optional maximum length
array_typet make_char_array_type(
  const typet &element_type,
  const typet &index_type,
  optionalt<std::size_t> max_length);

#endif // CPROVER_SOLVERS_STRINGS_MAX_CONCRETE_CHAR_ARRAY_H

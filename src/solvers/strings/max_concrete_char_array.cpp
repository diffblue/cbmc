/*******************************************************************\

Module: Size limit to choose between variable- and fixed-size char arrays

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
///  Size limit to choose between variable- and fixed-size char arrays

#include "max_concrete_char_array.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>

/// Pure guess; TODO study what this should be.
/// Char arrays with max length <= this will be allocated with a fixed size
/// (assuming the perhaps-wasted space is worth the less-complex formula
/// generated for fixed-size arrays), while larger arrays will be allocated
/// with indefinite size assuming generally the wasted space is not worth it.
const std::size_t max_concrete_char_array_length = 256;

array_typet make_char_array_type(
  const typet &element_type,
  const typet &index_type,
  optionalt<std::size_t> max_length)
{
  exprt array_size = max_length && *max_length <= max_concrete_char_array_length
                       ? (exprt)from_integer(*max_length, index_type)
                       : (exprt)infinity_exprt{index_type};

  return array_typet{element_type, array_size};
}

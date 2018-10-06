/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "dstring.h"

#include <ostream>

std::ostream &dstringt::operator<<(std::ostream &out) const
{
  return out << as_string();
}

dstringt get_dstring_number(std::size_t value)
{
  static const dstringt *const dstring_numbers = [] {
    dstringt *array = new dstringt[DSTRING_NUMBERS_MAX + 1];
    for(std::size_t i = 0; i <= DSTRING_NUMBERS_MAX; i++)
      array[i] = dstringt(std::to_string(i));
    return array;
  }();

  return dstring_numbers[value];
}

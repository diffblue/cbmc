/*******************************************************************\

Module: Format vector of numbers into a compressed range

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Format vector of numbers into a compressed range

#ifndef CPROVER_UTIL_FORMAT_NUMBER_RANGE_H
#define CPROVER_UTIL_FORMAT_NUMBER_RANGE_H

#include "mp_arith.h"

#include <string>
#include <vector>

std::string format_number_range(const std::vector<mp_integer> &);

/// Parse a compressed range into a vector of numbers,
/// e.g. "2,4-6" -> [2,4,5,6]
std::vector<mp_integer> parse_number_range(const std::string &);

#endif // CPROVER_UTIL_FORMAT_NUMBER_RANGE_H

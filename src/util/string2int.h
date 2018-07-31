/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_UTIL_STRING2INT_H
#define CPROVER_UTIL_STRING2INT_H

#include "mp_arith.h"

#include <string>

// These check that the string is indeed a valid number,
// and fail an assertion otherwise.
// We use those for data types that C++11's std::stoi etc. do not
// cover.
unsigned
safe_string2unsigned(const std::string &str, int base = DECIMAL_SYSTEM);
std::size_t
safe_string2size_t(const std::string &str, int base = DECIMAL_SYSTEM);

// The below mimic C's atoi/atol: any errors are silently ignored.
// They are meant to replace atoi/atol.
int unsafe_string2int(const std::string &str, int base = DECIMAL_SYSTEM);
unsigned
unsafe_string2unsigned(const std::string &str, int base = DECIMAL_SYSTEM);
std::size_t
unsafe_string2size_t(const std::string &str, int base = DECIMAL_SYSTEM);

// Same for atoll
long long int
unsafe_string2signedlonglong(const std::string &str, int base = DECIMAL_SYSTEM);
long long unsigned int unsafe_string2unsignedlonglong(
  const std::string &str,
  int base = DECIMAL_SYSTEM);

#endif // CPROVER_UTIL_STRING2INT_H

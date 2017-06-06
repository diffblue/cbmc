/*******************************************************************\

Module: string hashing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// string hashing

#ifndef CPROVER_UTIL_STRING_HASH_H
#define CPROVER_UTIL_STRING_HASH_H

#include <string>

size_t hash_string(const std::string &s);
size_t hash_string(const char *s);

// NOLINTNEXTLINE(readability/identifiers)
struct string_hash
{
  size_t operator()(const std::string &s) const { return hash_string(s); }
};

#endif // CPROVER_UTIL_STRING_HASH_H

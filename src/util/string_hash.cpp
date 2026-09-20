/*******************************************************************\

Module: string hashing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// string hashing

#include "string_hash.h"

std::size_t hash_string(std::string_view s)
{
  return hash_string(s.data(), s.size());
}

std::size_t hash_string(const char *s, std::size_t len)
{
  std::size_t h = 0;

  for(; len != 0; --len, ++s)
    h = (h << 5) - h + *s;

  return h;
}

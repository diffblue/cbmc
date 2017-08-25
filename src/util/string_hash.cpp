/*******************************************************************\

Module: string hashing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// string hashing

#include "string_hash.h"

size_t hash_string(const std::string &s)
{
  size_t h=0;
  size_t size=s.size();

  for(unsigned i=0; i<size; i++)
    h=(h<<5)-h+s[i];

  return h;
}

size_t hash_string(const char *s)
{
  size_t h=0;

  for(; *s!=0; s++)
    h=(h<<5)-h+*s;

  return h;
}

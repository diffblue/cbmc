/*******************************************************************\

Module: MurmurHash3 finalisation mixers

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

/// \file
/// MurmurHash3 finalisation ("fmix") mixers, forcing all bits of a hash to
/// avalanche. Shared by irep_hash.h (irep hash combining) and string_hash.cpp
/// (string hashing) so the constants have exactly one definition.

#ifndef CPROVER_UTIL_MURMUR_FINALIZER_H
#define CPROVER_UTIL_MURMUR_FINALIZER_H

#include <cstdint>

/// MurmurHash3 32-bit finalisation mix.
inline std::uint32_t murmur_fmix32(std::uint32_t h)
{
  h ^= h >> 16;
  h *= 0x85ebca6bu;
  h ^= h >> 13;
  h *= 0xc2b2ae35u;
  h ^= h >> 16;

  return h;
}

/// MurmurHash3 64-bit finalisation mix.
inline std::uint64_t murmur_fmix64(std::uint64_t h)
{
  // a brief experiment with supposedly better constants from
  // http://zimbry.blogspot.co.uk/2011/09/better-bit-mixing-improving-on.html
  // rather resulted in a slightly worse result
  h ^= h >> 33;
  h *= 0xff51afd7ed558ccdULL;
  h ^= h >> 33;
  h *= 0xc4ceb9fe1a85ec53ULL;
  h ^= h >> 33;

  return h;
}

#endif // CPROVER_UTIL_MURMUR_FINALIZER_H

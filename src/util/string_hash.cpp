/*******************************************************************\

Module: string hashing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// string hashing

#include "string_hash.h"

#include "murmur_finalizer.h"

#include <cstdint>

// Use a hash with good avalanche properties for CBMC's symbol names,
// which often share long common prefixes (e.g., main::1::x!0@1#1).
//
// We pick the FNV-1a variant width to match `std::size_t` so that
// 32-bit builds use 32-bit constants and arithmetic (avoiding libgcc
// 64-bit multiplication helpers) and 64-bit builds use the wider
// 64-bit variant. The Murmur fmix finalizer is applied at the end for
// additional avalanche.
//
// Note: the const char * overload below does a strlen() pass followed
// by a second pass over the bytes here. A single pass is not possible
// while mixing the length in first (which is what distinguishes a
// string from its prefixes), and folding the length in last would make
// the two overloads disagree for the same string. For CBMC's short
// identifiers the extra strlen (usually vectorised) is negligible.

static inline std::size_t hash_string_impl(const char *data, std::size_t len)
{
  static_assert(
    sizeof(std::size_t) == 4 || sizeof(std::size_t) == 8,
    "hash_string supports only 32-bit and 64-bit std::size_t");

  // `if constexpr` so each compilation only instantiates the branch
  // that matches the platform's `std::size_t` width. With two
  // separate template specialisations clang's `-Wunused-function`
  // would correctly point out that the unused width is unused.
  if constexpr(sizeof(std::size_t) == 8)
  {
    // FNV-1a-64.
    std::uint64_t h = 0xcbf29ce484222325ULL; // offset basis
    // Mix in the length first to differentiate strings that are
    // prefixes of each other.
    h ^= len;
    for(std::size_t i = 0; i < len; ++i)
      h = (h ^ static_cast<unsigned char>(data[i])) * 0x100000001b3ULL; // prime
    return static_cast<std::size_t>(murmur_fmix64(h));
  }
  else
  {
    // FNV-1a-32.
    std::uint32_t h = 0x811c9dc5u; // offset basis
    h ^= static_cast<std::uint32_t>(len);
    for(std::size_t i = 0; i < len; ++i)
      h = (h ^ static_cast<unsigned char>(data[i])) * 0x01000193u; // prime
    return murmur_fmix32(h);
  }
}

std::size_t hash_string(std::string_view s)
{
  return hash_string_impl(s.data(), s.size());
}

std::size_t hash_string(const char *s, std::size_t len)
{
  return hash_string_impl(s, len);
}

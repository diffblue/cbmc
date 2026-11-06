/*******************************************************************\

Module: Unit tests for string_hash.h

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/string_hash.h>

#include <testing-utils/use_catch.h>

#include <bitset>
#include <set>
#include <string>

TEST_CASE(
  "hash_string is deterministic for equal inputs",
  "[core][util][string_hash]")
{
  // Pure determinism: equal inputs map to equal hash values, no matter
  // whether we go through the std::string overload or the const char *
  // overload, and no matter how many times we compute it.
  const std::string s = "main::1::x!0@1#1";
  REQUIRE(hash_string(s) == hash_string(s));
  REQUIRE(hash_string(s) == hash_string(s.c_str()));
  REQUIRE(hash_string("") == hash_string(std::string{}));
}

TEST_CASE(
  "hash_string distinguishes two-character strings that differ in one bit",
  "[core][util][string_hash]")
{
  // The classic worst-case for hash functions with poor avalanche: tiny
  // inputs that differ in a single bit. FNV-1a with the Murmur fmix
  // finalizer should map these to clearly distinct hash values.
  CHECK(hash_string("a") != hash_string("b"));
  CHECK(hash_string("ab") != hash_string("ac"));
  CHECK(hash_string("ab") != hash_string("aa"));
  CHECK(hash_string("ab") != hash_string("ba"));
}

TEST_CASE(
  "hash_string distinguishes strings that are prefixes of one another",
  "[core][util][string_hash]")
{
  // CBMC produces lots of SSA-renamed symbol names that share long
  // common prefixes (e.g., main::1::x!0@1#1, main::1::x!0@1#2). Mixing
  // the length into the hash before processing the bytes ensures that
  // a string and any of its prefixes hash to different values.
  CHECK(hash_string("main::1::x") != hash_string("main::1::x!"));
  CHECK(hash_string("main::1::x!0@1#1") != hash_string("main::1::x!0@1#11"));
  CHECK(hash_string("") != hash_string("a"));
}

TEST_CASE(
  "hash_string has acceptable distribution on CBMC-style symbol names",
  "[core][util][string_hash]")
{
  // Sanity check: hashing a small batch of CBMC-style SSA-renamed
  // symbol names should produce no collisions at all in 64-bit (and
  // very few in 32-bit). The previous djb2-variant hash would
  // collide noticeably on inputs of this shape, which is what
  // motivated this change.
  std::set<std::size_t> seen;
  std::size_t inserted = 0;
  for(int frame = 0; frame < 16; ++frame)
  {
    for(int var = 0; var < 16; ++var)
    {
      for(int ssa = 0; ssa < 16; ++ssa)
      {
        const std::string name = "main::" + std::to_string(frame) + "::x" +
                                 std::to_string(var) + "!0@1#" +
                                 std::to_string(ssa);
        seen.insert(hash_string(name));
        ++inserted;
      }
    }
  }
  // 64-bit: zero collisions expected. 32-bit: birthday bound predicts ~0.002
  // expected collisions for 4096 inputs hashed to 32 bits, so requiring at
  // least 4090 unique values leaves comfortable headroom while still being
  // tight enough to catch a hash regression on this workload.
  REQUIRE(seen.size() >= inserted - 6);
}

TEST_CASE(
  "hash_string has avalanche: flipping one input bit flips ~half the output",
  "[core][util][string_hash]")
{
  // Avalanche criterion: flipping a single bit of the input should, on
  // average, flip about half of the output bits. This is the property the
  // Murmur fmix finalizer is there to provide; a hash that merely passed the
  // hand-picked pairs above (e.g. one keyed only on the first byte) would
  // fail here.
  const std::string base = "main::1::x!0@1#1";
  const std::size_t reference = hash_string(base);
  constexpr std::size_t hash_bits = sizeof(std::size_t) * 8;

  std::size_t total_flipped = 0;
  std::size_t trials = 0;
  for(std::size_t byte = 0; byte < base.size(); ++byte)
  {
    for(int bit = 0; bit < 8; ++bit)
    {
      std::string flipped = base;
      flipped[byte] = static_cast<char>(flipped[byte] ^ (1 << bit));
      const std::size_t diff = hash_string(flipped) ^ reference;
      total_flipped += std::bitset<hash_bits>(diff).count();
      ++trials;
    }
  }

  const double average = static_cast<double>(total_flipped) / trials;
  REQUIRE(average >= 0.25 * hash_bits);
  REQUIRE(average <= 0.75 * hash_bits);
}

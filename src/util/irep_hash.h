/*******************************************************************\

Module: irep hash functions

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

#ifndef CPROVER_IREP_HASH_H
#define CPROVER_IREP_HASH_H

// you need to pick one of the following options

#define IREP_HASH_BASIC
// #define IREP_HASH_MURMURHASH2A
// #define IREP_HASH_MURMURHASH3

// Comparison for OS X, 64 bit, LLVM version 5.1:
//
// On the regression test suite (cbmc), BASIC 55 times leads to fewer
// calls to irept::operator==, and 210 times MURMURHASH3 results in
// fewer calls; BASIC has a total of 1479007 calls, whereas
// MURMURHASH3 has 1455539 calls; worst case of BASIC improving over
// MURMURHASH3 is strtol1 with 4696 fewer calls (3.0%); best case of
// MURMURHASH3 improving over BASIC with 1893 fewer calls (3.5%) is
// Double-to-float-with-simp1
//
// Comparing BASIC and MURMURHASH2A, we have 72 cases with fewer calls
// in BASIC, and 195 cases with MURMURHASH2A having fewer calls at a
// total of 1454334 calls; BASIC improves the most over MURMURHASH2A
// on Double-to-float-with-simp1 with 3367 fewer calls (6.3%), while
// MURMURHASH2A compares most favourably on String6 with 3076 fewer
// calls (2.9%)

#include <cstddef> // std::size_t

#ifdef _MSC_VER

#  define FORCE_INLINE    __forceinline

#  include <cstdint>
#  include <cstdlib>

#  define ROTL32(x,y)     _rotl(x,y)
#  define ROTL64(x,y)     _rotl64(x,y)

#  define BIG_CONSTANT(x) (x)

#else   // !_MSC_VER

#  define FORCE_INLINE inline __attribute__((always_inline))

#  include <stdint.h>

static FORCE_INLINE uint32_t ROTL32(uint32_t x, int8_t r)
{
  return (x << r) | (x >> (32 - r));
}

static FORCE_INLINE uint64_t ROTL64(uint64_t x, int8_t r)
{
  return (x << r) | (x >> (64 - r));
}

#  define BIG_CONSTANT(x) (x##LLU)

#endif


#ifdef IREP_HASH_BASIC

template<int>
std::size_t basic_hash_combine(
  std::size_t h1,
  std::size_t h2);

/*******************************************************************\

Function: basic_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<>
inline std::size_t basic_hash_combine<32>(
  std::size_t h1,
  std::size_t h2)
{
  return ROTL32(h1, 7)^h2;
}

/*******************************************************************\

Function: basic_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<>
inline std::size_t basic_hash_combine<64>(
  std::size_t h1,
  std::size_t h2)
{
  #ifdef _MSC_VER
  // The below intentionally limits the hash key to 32 bits.
  // This is because Visual Studio's STL masks away anything
  // but the least significant n bits, where 2^n is the size of
  // the hash table. On systems with 64-bit size_t, we then see
  // performance degradation as too much of the hash key is
  // contained in bits that will be masked away. There is no such
  // issue when using the GNU C++ STL.

  unsigned int int_value=(unsigned)h1; // lose data here
  return ROTL32(int_value, 7)^h2;
  #else
  return ROTL64(h1, 7)^h2;
  #endif
}

/*******************************************************************\

Function: basic_hash_finalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static inline std::size_t basic_hash_finalize(
  std::size_t h1,
  std::size_t len)
{
  (void)len;

  return h1;
}

#define hash_combine(h1, h2) \
  basic_hash_combine<sizeof(std::size_t)*8>(h1, h2)
#define hash_finalize(h1, len) \
  basic_hash_finalize(h1, len)

#endif


#ifdef IREP_HASH_MURMURHASH2A

// Based on Austin Appleby's MurmurHash2A:
// https://code.google.com/p/pyfasthash/source/browse/trunk/src/MurmurHash/MurmurHash2A.cpp?r=19
// 64 bit constants taken from
// https://code.google.com/p/pyfasthash/source/browse/trunk/src/MurmurHash/MurmurHash2_64.cpp?r=19

template<int>
std::size_t murmurhash2a_hash_combine(
  std::size_t h1,
  std::size_t h2);

template<int>
std::size_t murmurhash2a_hash_finalize(
  std::size_t h1,
  std::size_t len);

/*******************************************************************\

Function: murmurhash2a_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static FORCE_INLINE uint32_t mmix32(uint32_t h1, uint32_t h2)
{
  const int r=24;
  const uint32_t m=0x5bd1e995;

  h2*=m;
  h2^=h2 >> r;
  h2*=m;
  h1*=m;
  h1^=h2;

  return h1;
}

template<>
inline std::size_t murmurhash2a_hash_combine<32>(
  std::size_t h1,
  std::size_t h2)
{
  return mmix32(h1, h2);
}

/*******************************************************************\

Function: murmurhash2a_hash_finalize

  Inputs:

 Outputs:

 Purpose: force all bits of a hash block to avalanche

\*******************************************************************/

template<>
inline std::size_t murmurhash2a_hash_finalize<32>(
  std::size_t h1,
  std::size_t len)
{
  const uint32_t m=0x5bd1e995;

  h1=mmix32(h1, len);

  h1^=h1 >> 13;
  h1*=m;
  h1^=h1 >> 15;

  return h1;
}

/*******************************************************************\

Function: murmurhash2a_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static FORCE_INLINE uint64_t mmix64(uint64_t h1, uint64_t h2)
{
  const int r=47;
  const uint64_t m=0xc6a4a7935bd1e995;

  h2*=m;
  h2^=h2 >> r;
  h2*=m;
  // the original 64bit (non-incremental) algorithm swaps the
  // following two operations
  h1*=m;
  h1^=h2;

  return h1;
}

template<>
inline std::size_t murmurhash2a_hash_combine<64>(
  std::size_t h1,
  std::size_t h2)
{
  return mmix64(h1, h2);
}

/*******************************************************************\

Function: murmurhash2a_hash_finalize

  Inputs:

 Outputs:

 Purpose: force all bits of a hash block to avalanche

\*******************************************************************/

template<>
inline std::size_t murmurhash2a_hash_finalize<64>(
  std::size_t h1,
  std::size_t len)
{
  const int r=47;
  const uint64_t m=0xc6a4a7935bd1e995;

  // not in the original code
  h1=mmix64(h1, len);

  h1^=h1 >> r;
  h1*=m;
  h1^=h1 >> r;

  return h1;
}

#define hash_combine(h1, h2) \
  murmurhash2a_hash_combine<sizeof(std::size_t)*8>(h1, h2)
#define hash_finalize(h1, len) \
  murmurhash2a_hash_finalize<sizeof(std::size_t)*8>(h1, len)

#endif


#ifdef IREP_HASH_MURMURHASH3

// Based on MurmurHash3, originally implemented by Austin Appleby who
// placed the code in the public domain, disclaiming any copyright.
// See the original source for details and further comments:
// https://code.google.com/p/smhasher/source/browse/trunk/MurmurHash3.cpp

template<int>
std::size_t murmurhash3_hash_combine(
  std::size_t h1,
  std::size_t h2);

template<int>
std::size_t murmurhash3_hash_finalize(
  std::size_t h1,
  std::size_t len);

/*******************************************************************\

Function: murmurhash3_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<>
inline std::size_t murmurhash3_hash_combine<32>(
  std::size_t h1,
  std::size_t h2)
{
  const uint32_t c1=0xcc9e2d51;
  const uint32_t c2=0x1b873593;

  h2*=c1;
  h2=ROTL32(h2,15);
  h2*=c2;

  h1^=h2;
  h1=ROTL32(h1,13);
  h1=h1*5+0xe6546b64;

  return h1;
}

/*******************************************************************\

Function: murmurhash3_hash_finalize

  Inputs:

 Outputs:

 Purpose: force all bits of a hash block to avalanche

\*******************************************************************/

static FORCE_INLINE uint32_t fmix32(uint32_t h)
{
  h^=h >> 16;
  h*=0x85ebca6b;
  h^=h >> 13;
  h*=0xc2b2ae35;
  h^=h >> 16;

  return h;
}

template<>
inline std::size_t murmurhash3_hash_finalize<32>(
  std::size_t h1,
  std::size_t len)
{
  h1^=len;

  return fmix32(h1);
}

/*******************************************************************\

Function: murmurhash3_hash_combine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<>
inline std::size_t murmurhash3_hash_combine<64>(
  std::size_t h1,
  std::size_t h2)
{
  const std::size_t h1_tmp=h1;

  const uint64_t c1=BIG_CONSTANT(0x87c37b91114253d5);
  const uint64_t c2=BIG_CONSTANT(0x4cf5ad432745937f);

  h2*=c1;
  h2=ROTL64(h2,31);
  h2*=c2;

  h1^=h2;
  h1=ROTL64(h1,27);
  // it may be better to omit the following re-combination according
  // to the LLBMC benchmark set (reduces the hash collisions in
  // boolbv_width::get_entry, but slightly increases them elsewhere)
  h1+=h1_tmp;
  h1=h1*5+0x52dce729;

  return h1;
}

/*******************************************************************\

Function: murmurhash3_hash_finalize

  Inputs:

 Outputs:

 Purpose: force all bits of a hash block to avalanche

\*******************************************************************/

static FORCE_INLINE uint64_t fmix64(uint64_t h)
{
  // a brief experiment with supposedly better constants from
  // http://zimbry.blogspot.co.uk/2011/09/better-bit-mixing-improving-on.html
  // rather resulted in a slightly worse result
  h^=h >> 33;
  h*=BIG_CONSTANT(0xff51afd7ed558ccd);
  h^=h >> 33;
  h*=BIG_CONSTANT(0xc4ceb9fe1a85ec53);
  h^=h >> 33;

  return h;
}

template<>
inline std::size_t murmurhash3_hash_finalize<64>(
  std::size_t h1,
  std::size_t len)
{
  h1^=len;

  return fmix64(h1);
}

#define hash_combine(h1, h2) \
  murmurhash3_hash_combine<sizeof(std::size_t)*8>(h1, h2)
#define hash_finalize(h1, len) \
  murmurhash3_hash_finalize<sizeof(std::size_t)*8>(h1, len)

#endif

#endif

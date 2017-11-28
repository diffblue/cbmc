#include <assert.h>
#include <stdint.h>

#ifndef __GNUC__
uint16_t __builtin_bswap16(uint16_t);
uint32_t __builtin_bswap32(uint32_t);
uint64_t __builtin_bswap64(uint64_t);
#endif

uint16_t __VERIFIER_nondet_u16();
uint32_t __VERIFIER_nondet_u32();
uint64_t __VERIFIER_nondet_u64();

int main()
{
  uint16_t sa = 0xabcd;
  assert(__builtin_bswap16(sa) == 0xcdab);
  uint16_t sb = __VERIFIER_nondet_u16();
  sb &= 0xff00;
  // expected to fail, only MSB guaranteed to be 0
  assert(__builtin_bswap16(sb) == 0);
  assert((__builtin_bswap16(sb) & 0xff00) == 0);

  uint32_t a = 0xabcdef00;
  assert(__builtin_bswap32(a) == 0x00efcdab);
  uint32_t b = __VERIFIER_nondet_u32();
  b &= 0xffffff00;
  // expected to fail, only MSB guaranteed to be 0
  assert(__builtin_bswap32(b) == 0);
  assert((__builtin_bswap32(b) & 0xff000000) == 0);

  uint64_t al = 0xabcdef0001020304LL;
  assert(__builtin_bswap64(al) == 0x0403020100efcdabLL);
  uint64_t bl = __VERIFIER_nondet_u64();
  bl &= 0xffffffffffffff00LL;
  // expected to fail, only MSB guaranteed to be 0
  assert(__builtin_bswap64(bl) == 0);
  assert((__builtin_bswap64(bl) & 0xff00000000000000) == 0);

  return 0;
}

#include <stdint.h>

#ifndef __GNUC__
uint16_t __builtin_bswap16(uint16_t);
uint32_t __builtin_bswap32(uint32_t);
#endif

int main()
{
  uint32_t a = 0x12345678u;
  __CPROVER_assert(__builtin_bswap32(a) == 0x78563412u, "bswap32");

  uint16_t b = 0xABCDu;
  __CPROVER_assert(__builtin_bswap16(b) == 0xCDABu, "bswap16");
}

#include <stdint.h>

int main()
{
  _Bool c;
  uint8_t raw[16] = {0};
  raw[12] = 0xAA;

  // The value set of p contains two entries for raw: the whole array (at
  // offset 0) and the element raw[12] (at offset 12).
  const void *p = c ? (const void *)(raw + 12) : (const void *)&raw;

  __CPROVER_assert(*(const uint8_t *)p == (c ? 0xAA : 0), "correct byte");
  return 0;
}

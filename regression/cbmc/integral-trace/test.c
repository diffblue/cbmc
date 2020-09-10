#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

int main()
{
  int8_t i1 = 2;
  int16_t i2 = 3;
  int32_t i3 = 4;
  int64_t i4 = 5;

  int8_t in1 = -2;
  int16_t in2 = -3;
  int32_t in3 = -4;
  int64_t in4 = -5;

  uint8_t u8 = 'a';
  uint16_t u16 = 8;
  uint32_t u32 = 16;
  uint64_t u64 = 32;

  void *ptr = malloc(1);

  assert(false);

  return 0;
}

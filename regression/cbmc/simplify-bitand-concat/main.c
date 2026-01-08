#include <assert.h>
#include <stdint.h>

// Reinterpreting the bytes of a multi-byte integer produces, during symbolic
// execution, a bitwise-and of a concatenation of the individual bytes with a
// constant mask.  The simplifier distributes the mask over the concatenation
// and simplifies each slice (an all-zero mask slice yields a zero byte, an
// all-one slice yields the byte unchanged).  This test exercises that path
// end-to-end.

union u32_bytes
{
  uint32_t value;
  uint8_t bytes[4];
};

int main()
{
  union u32_bytes u;
  uint8_t b0, b1, b2, b3;
  u.bytes[0] = b0;
  u.bytes[1] = b1;
  u.bytes[2] = b2;
  u.bytes[3] = b3;

  // Little-endian: bytes[0] is the least significant byte.  The mask keeps
  // bytes 0 and 2 (all-one slices) and clears bytes 1 and 3 (all-zero slices).
  const uint32_t masked = u.value & 0x00FF00FFu;

  assert((masked & 0xFFu) == b0);
  assert(((masked >> 8) & 0xFFu) == 0u);
  assert(((masked >> 16) & 0xFFu) == b2);
  assert(((masked >> 24) & 0xFFu) == 0u);

  return 0;
}

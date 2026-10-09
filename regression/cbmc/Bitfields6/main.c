// System V ABI / GCC: a bit-field must be contained in a storage unit of its
// declared type; one that does not fit in what remains of the current unit
// starts at the next one, and the remaining bits are padding.  `c' (5 bits)
// does not fit after a:6, r:1, b:4 -- it starts in byte 2, and the plain
// member `d' follows in byte 3 (dense packing would place d in byte 2).
#include <stdint.h>

struct B7
{
  uint8_t a : 6;
  uint8_t r : 1;
  uint8_t b : 4;
  uint8_t c : 5;
  uint8_t d;
};

int main()
{
  __CPROVER_assert(sizeof(struct B7) == 4, "size");
  struct B7 x = {0};
  x.d = 0xAB;
  x.c = 17;
  x.b = 9;
  x.a = 33;
  x.r = 1;
  unsigned char *p = (unsigned char *)&x;
  __CPROVER_assert(p[3] == 0xAB, "d in byte 3");
  __CPROVER_assert(
    p[0] == (33 | (1 << 6)) && p[1] == 9 && p[2] == 17, "byte layout");
  __CPROVER_assert(x.c == 17 && x.b == 9 && x.a == 33 && x.r == 1, "values");
  return 0;
}

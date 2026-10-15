#include <assert.h>

struct S2
{
  signed r : 2;
};
struct S1
{
  signed r : 1;
};
struct S7
{
  signed r : 7;
};
struct U3
{
  unsigned r : 3;
};
struct S32
{
  signed r : 32;
};

static int outer;
static struct S2 s2;
static struct S1 s1;
static struct S7 s7;
static struct U3 u3;
static struct S32 s32;

int main(void)
{
  // Per C11 6.5.16.1p3, the value of an assignment expression is the value of
  // the left operand after the assignment. For a signed bit-field that is the
  // stored value masked to the field width and then sign-extended. Each case
  // below is a chained assignment `outer = bf = expr`, which goto-conversion
  // lowers through a bit-field temporary -- the construct this fix is about.

  // 2-bit signed, positive RHS: 2 -> bits 10 -> -2
  outer = s2.r = 2;
  assert(outer == -2);
  assert((int)s2.r == -2);

  // 2-bit signed, negative RHS: -3 -> bits 01 -> +1
  outer = s2.r = -3;
  assert(outer == 1);
  assert((int)s2.r == 1);

  // 1-bit signed boundary: 1 -> -1 (sign_bit == mask == 1)
  outer = s1.r = 1;
  assert(outer == -1);
  assert((int)s1.r == -1);

  // 7-bit signed with high bit set: 64 -> -64 (formula scales beyond 2 bits)
  outer = s7.r = 64;
  assert(outer == -64);
  assert((int)s7.r == -64);

  // unsigned 3-bit: unchanged AND-mask branch, 13 & 7 -> 5
  outer = u3.r = 13;
  assert(outer == 5);
  assert((int)u3.r == 5);

  // full-width (32-bit) signed: bf_width == underlying width, so this is
  // routed through the AND-mask branch with no narrowing: -3 stays -3
  outer = s32.r = -3;
  assert(outer == -3);
  assert((int)s32.r == -3);

  return 0;
}

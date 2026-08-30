#include <assert.h>

struct S
{
  signed f : 3;
};

static struct S s = {-1};

int main(void)
{
  // s.f = -1 (3-bit: 111), 8 = 0b1000
  // s.f &= 8: sign-extend -1 to 0xFFFFFFFF, & 8 = 8, truncate to 3 bits = 0
  // So (s.f &= 8) evaluates to 0 (the truncated value)
  // 0 || 0 = 0
  int x = (s.f &= 8) || 0;
  assert(x == 0);
  return 0;
}

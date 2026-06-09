#include <assert.h>

int g;
int h(void)
{
  g = 42;
  return 1;
}

int main(void)
{
  // folding __builtin_strlen to a constant must not lose side effects of its
  // argument; such calls are not folded
  unsigned long a = __builtin_strlen(h() ? "ab" : "ab");
  assert(g == 42);
  unsigned long b = __builtin_strlen("abc" + 0 * (g = 7));
  assert(g == 7);

  // calls without side effects are folded
  unsigned long c = __builtin_strlen("abc" + 1);
  assert(c == 2);
  return 0;
}

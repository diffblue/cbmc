#include <assert.h>

struct S2
{
  signed char f0;
  unsigned short f1;
};

union U10 {
  unsigned short f0;
  struct S2 f3;
};

union U10 g_2110 = {.f0 = 53747};
union U10 g_1256 = {-6L};

union U6 {
  signed f0 : 3;
};

union U6 g_1197 = {1L};

union U4 {
  signed f0 : 6;
  int f3;
};

union U4 g_1408 = {-1L};

int main()
{
  assert(g_2110.f0 == 53747);

  return 0;
}

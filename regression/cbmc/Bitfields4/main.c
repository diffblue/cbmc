#include <assert.h>
#include <stdint.h>

struct S0
{
  signed int f1 : 2;
};

int main(int argc, char *argv[])
{
  struct S0 l_4590 = {1};
  uint32_t g_307 = ++l_4590.f1;
  assert(g_307 == 4294967294u);

  l_4590 = (struct S0){1};
  uint32_t g_308 = l_4590.f1 += 1;
  assert(g_308 == 4294967294u);

  uint32_t g_309 = l_4590.f1 = 62378u;
  assert(g_309 == 4294967294u);
}

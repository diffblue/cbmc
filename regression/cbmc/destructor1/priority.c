#include <assert.h>

#ifdef __GNUC__
// GCC runs destructors in the reverse order of constructors: in descending
// priority order, with destructors of equal priority in the reverse of the
// order they appear in the program. A destructor without a priority has
// priority 65535.
int order[5];
int n;

__attribute__((destructor(101))) static void a_101(void)
{
  order[n++] = 5;
  // this destructor runs last
  assert(n == 5);
  for(int i = 0; i < 5; ++i)
    assert(order[i] == i + 1);
  // demonstrates that the destructors were run at all
  assert(0);
}
__attribute__((destructor(150 + 50))) static void b_200(void)
{
  order[n++] = 3;
}
__attribute__((destructor(200))) static void c_200(void)
{
  order[n++] = 2;
}
__attribute__((destructor)) static void d_no_priority(void)
{
  order[n++] = 1;
}
__attribute__((destructor((102)))) static void e_102(void)
{
  order[n++] = 4;
}
#endif

int main()
{
#ifdef __GNUC__
  assert(n == 0);
#else
  assert(0);
#endif
  return 0;
}

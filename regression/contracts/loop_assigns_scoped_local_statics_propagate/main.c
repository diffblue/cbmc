#include <assert.h>
#include <stdbool.h>

int j;

int before_loop()
{
  static int __static_local;
  __static_local = 0;
  return __static_local;
}

int after_loop()
{
  static int __static_local;
  __static_local = 0;
  return __static_local;
}

int bar(int i) __CPROVER_requires(true) __CPROVER_ensures(j == i)
  __CPROVER_assigns(j)
{
  static int __static_local;
  __static_local = 0;
  j = i;
  return __static_local;
}

int main()
{
  assert(before_loop() == 0);

  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_assigns(i, j)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    __CPROVER_loop_invariant(i != 0 ==> j + 1 == i)
    // clang-format on
    {
      bar(i);
    }

  assert(j == 9);
  assert(before_loop() == 0);
  assert(after_loop() == 0);
}

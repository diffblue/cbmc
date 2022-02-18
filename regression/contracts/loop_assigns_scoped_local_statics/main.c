#include <assert.h>

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

int lowerbound()
{
  static int __static_local;
  __static_local = 0;
  return 0;
}

int upperbound()
{
  static int __static_local;
  __static_local = 0;
  return 10;
}

void incr(int *i)
{
  static int __static_local;
  __static_local = 0;
  (*i)++;
}

int body_1(int i)
{
  static int __static_local;
  __static_local = 0;
  j = i;
  return __static_local;
}

int body_2(int *i)
{
  static int __static_local;
  __static_local = 0;
  (*i)++;
  (*i)--;
  return __static_local;
}

int body_3(int *i)
{
  static int __static_local;
  __static_local = 0;
  (*i)++;
  if(*i == 4)
    return 1;

  (*i)--;
  return 0;
}

int main()
{
  assert(before_loop() == 0);

  for(int i = lowerbound(); i < upperbound(); incr(&i))
    // clang-format off
    __CPROVER_assigns(i, j)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    __CPROVER_loop_invariant(i != 0 ==> j + 1 == i)
    // clang-format on
    {
      body_1(i);

      if(body_3(&i))
        return 1;

      body_2(&i);
    }

  assert(j == 9);
  assert(before_loop() == 0);
  assert(after_loop() == 0);
}

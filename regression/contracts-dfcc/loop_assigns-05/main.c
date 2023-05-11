#include <assert.h>

int j;

int lowerbound()
{
  return 0;
}

int upperbound()
{
  return 10;
}

void incr(int *i)
{
  (*i)++;
}

void body_1(int i)
{
  j = i;
}

void body_2(int *i)
{
  (*i)++;
  (*i)--;
}

int body_3(int *i)
{
  (*i)++;
  if(*i == 4)
    return 1;

  (*i)--;
  return 0;
}

int main()
{
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
}

<<<<<<< HEAD
#include <assert.h>

struct S
{
  int x;
};

struct T
{
  struct S a[2];
=======
struct test_struct
{
  int a[2];
  int b;
>>>>>>> 2846e8c... Explicitly initialise non-static objects with non-deterministic values
};

int main()
{
<<<<<<< HEAD
  struct T t;
  t.a[1].x = 42;
  assert(t.a[1].x == 42);
  return 0;
=======
  struct test_struct test;
  test.a[1] = 1;
  test.b = 1;
  __CPROVER_assert(test.a[1] == 0, "");
>>>>>>> 2846e8c... Explicitly initialise non-static objects with non-deterministic values
}

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int baz() __CPROVER_requires(true) __CPROVER_ensures(true) __CPROVER_assigns()
{
  static int __local_static = 0;
  __local_static = 0;

  return __local_static;
}

int bar() __CPROVER_requires(true) __CPROVER_ensures(true) __CPROVER_assigns()
{
  static int __local_static_arr[2];
  __local_static_arr[0] = 0;
  __local_static_arr[1] = 0;

  baz();
  return __local_static_arr[0] | __local_static_arr[1];
}

void foo() __CPROVER_requires(true) __CPROVER_ensures(true) __CPROVER_assigns()
{
  bar();
}

int main()
{
  foo();
  __CPROVER_assert(baz() == 0, "expecting FAILURE");
  __CPROVER_assert(bar() == 0, "expecting FAILURE");
}

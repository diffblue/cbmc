#include <assert.h>

int global;

void simple_function(void)
{
  int j = 0;
}

void pointer_function(int *write_to, int value)
{
  *write_to = value;
}

void modify_global_function(int new_val)
{
  global = new_val;
}

void simple_test()
{
  int i = 0;
  global = 0;
  simple_function();
  __CPROVER_assert(i == 0, "i==0");
  __CPROVER_assert(global == 0, "global==0");

  i = 1;
  global = 2;
  simple_function();
  __CPROVER_assert(i == 1, "i==1");
  __CPROVER_assert(global == 2, "global==2");
}

void pointer_test()
{
  int i = 0;
  int j = 1;
  pointer_function(&i, 10);

  __CPROVER_assert(j == 1, "j==1");
  __CPROVER_assert(i == 10, "i==10");

  j = 2;
  pointer_function(&i, 10);

  __CPROVER_assert(j == 2, "j==2");
  __CPROVER_assert(i == 10, "i==10");

  j = 3;
  pointer_function(&i, 11);

  __CPROVER_assert(j == 3, "j==3");
  __CPROVER_assert(
    i == 11, "i==11"); // unknown since value has top for pointer_function

  j = 4;
  pointer_function(&i, 478);

  __CPROVER_assert(j == 4, "j==4");
  __CPROVER_assert(
    i == 11, "i==11"); // unknown since value has top for pointer_function
}

void global_test()
{
  global = 0;
  modify_global_function(42);
  __CPROVER_assert(global == 42, "global==42");

  modify_global_function(50);
  __CPROVER_assert(
    global == 50, "global==50"); // unknown since new_val will be top
}

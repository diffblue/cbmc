#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent pointers to pointers
  // Basic use of addresses
  int a=0;
  int *p=&a;
  int **x=&p;

  // Reading from a pointer to a pointer that's been dereferenced twice
  __CPROVER_assert(**x == 0, "**x==0");
  __CPROVER_assert(**x == 1, "**x==1");
  a=1;
  __CPROVER_assert(**x == 1, "**x==1");
  __CPROVER_assert(**x == 0, "**x==0");

  // Writing to a pointer to a pointer that's been dereferenced twice
  **x=2;
  __CPROVER_assert(a == 2, "a==2");
  __CPROVER_assert(a == 1, "a==1");

  return 0;
}

#include <assert.h>
#include <stdbool.h>

int main()
{
  int x;
  int y;
  int z;
  bool nondet1;
  bool nondet2;
  int *a = nondet1 ? &x : &y;
  int *b = nondet2 ? &y : &z;
  __CPROVER_assert(!__CPROVER_same_object(a, b), "Can be violated.");
}

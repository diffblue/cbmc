#include <stdbool.h>
#include <stdlib.h>

// type of functions that manipulate arrays
typedef void (*fun_t)(char *arr, size_t size);

void contract(char *arr, size_t size, bool b);

typedef void (*voidfun_t)(void);

voidfun_t identity(voidfun_t fun)
{
  return fun;
}

int foo(char *arr, size_t size, fun_t fun)
  __CPROVER_requires(__CPROVER_obeys_contract(fun, contract))
{
  return 0;
}

void main()
{
  size_t size;
  char *arr;
  fun_t fun;
  foo(arr, size, fun);
}

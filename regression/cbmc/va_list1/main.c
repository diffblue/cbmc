#include <assert.h>

int my_f(int x, ...)
{
  __builtin_va_list list;
  __builtin_va_start(list, x);
  
  int value;
  unsigned i;
  
  for(i=0; i<x; i++)
    value=__builtin_va_arg(list, int);

  __builtin_va_end(list);
  
  return value;
}

int my_h(__builtin_va_list list)
{
  __builtin_va_arg(list, int);
  return __builtin_va_arg(list, int);
}

int my_g(int x, ...)
{
  int result;
  __builtin_va_list list;
  __builtin_va_start(list, x);
  result=my_h(list);
  __builtin_va_end(list);
  return result;
}

int main()
{
  assert(my_f(3, 10, 20, 30)==30);
  assert(my_f(1, 10, 20, 30)==10);
  assert(my_f(1, 10)==10);
  assert(my_g(11, 22, 33)==33);
}

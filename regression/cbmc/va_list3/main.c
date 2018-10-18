#include <stdarg.h> 
#include <assert.h> 

void foo(int n, ...);

int main()
{
  foo(1, 1u);
  foo(2, 2l);
  foo(3, 3.0);
  return 0;
}

void foo(int n, ...)
{
  va_list vl;

  va_start(vl,n);
  
  switch(n)
  {
  case 1: assert(va_arg(vl, unsigned)==1); break;
  case 2: assert(va_arg(vl, long)==2); break;
  case 3: assert(va_arg(vl, double)==3.0); break;
  }
  
  va_end(vl);
}

#include <stdio.h> 
#include <stdarg.h> 
#include <assert.h> 

int max(int n, ...);

int main ()
{
  int m;
  int m2;
  int m3;

  m = max(3, 2, 6, 9);
  m2 = max(3, 4, 11, 1);

  m3 = max(2, m, m2);

  assert(m3 == 11);

  return 0;
}

int max(int n, ...)
{
  int i,val,largest;

  va_list vl;

  va_start(vl,n);
  largest=va_arg(vl,int);

  for (i=1;i<n;i++)
  {
    val=va_arg(vl,int);
    largest=(largest>val)?largest:val;
  }
 
  va_end(vl);

  return largest;
}

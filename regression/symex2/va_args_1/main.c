#include <stdio.h> 
#include <stdarg.h> 

int max(int n, ...);

int main ()
{
  int m;

  int y = 7;
  int u = 2;
  m = max(3, y, u, 9);

  assert(m == 9);

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

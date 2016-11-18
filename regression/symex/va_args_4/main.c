#include <stdio.h> 
#include <stdarg.h> 
#include <assert.h> 

int max(int n, ...);

int main()
{
  int m;
  m = max(2, 2, 8, 10);

  assert(m == 10);

  return 0;
}

int max(int repeat,int n, ...)
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
 
  for (i = 0; i < repeat; i++){
	  printf("%d. Result is: %d", i, largest);	
  }

 	va_end(vl);
  return largest;
}

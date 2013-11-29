#include <stdio.h>

int rec(int x)
{
  if(x==0) return x;
  printf(">>>>> x = %d\n", x);
  return rec(x-1)+1;
}

int main()
{
  int res=0;

  res=rec(3);
  res=res+rec(3);
  res=res+rec(3);
  res=res+rec(3);

  printf(">>>>> res = %d\n", res);

  assert(res==12);

  return res;
}

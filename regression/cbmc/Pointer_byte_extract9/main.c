#include <assert.h>

int main()
{
  int N;

  char a1[N];
  *((char *)a1)=1;
  *((int *)a1)=1;

  short a2[N];
  *((char *)a2)=1;
  *((int *)a2)=1;

  int a3[N];
  *((char *)a3)=1;
  *((int *)a3)=1;

  assert(0);
}

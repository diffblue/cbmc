#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main()
{
  int i, j;
  int val;
  int length = __VERIFIER_nondet_int();
  if(length < 1)
    length = 1;
  int *arr = malloc(length);
  if(!arr)
    return 0;
  for(i = 0; i < length; i++)
  {
    val = __VERIFIER_nondet_int();
    if(val < 0)
    {
      val = 0;
    }
    arr[i] = val;
  }
  for(j = 0; j < length; j++)
  {
    while(arr[j] > 0)
    {
      arr[j]--;
    }
  }
  return 0;
}

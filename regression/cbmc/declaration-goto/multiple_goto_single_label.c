#include <assert.h>

extern void __VERIFIER_assume(int cond);

int main(void)
{
  int l = 2;
  int if_condition1;
  if(if_condition1)
  {
    unsigned int j = 42;
    l = 3;
    goto merge_point;
  }
  int if_condition2;
  if(if_condition2)
  {
    l = 4;
    unsigned int k = 24;
    goto merge_point;
  }
  int i = 3;
  int m = 9;

merge_point:
  assert(i == 3 || m == 9 || l == 3);
  assert(i == 3 || m == 9 || l == 4);
  return 0;
}

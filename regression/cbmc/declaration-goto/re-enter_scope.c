#include <assert.h>

extern void __VERIFIER_assume(int cond);

int main(void)
{
  int if_condition;
  if(if_condition)
  {
    unsigned int i = 42;
    goto j_scope;
  i_scope:
    assert(i == 42);
    return 0;
  }
  int j = 3;
  assert(j == 3);

j_scope:
  assert(j == 3);
  if(if_condition)
    goto i_scope;
  return 0;
}

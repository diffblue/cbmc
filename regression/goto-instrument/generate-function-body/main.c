#include <assert.h>

void should_not_be_replaced(void)
{
  __CPROVER_assume(0);
}

void should_be_generated(void);

int main(void)
{
  int flag;
  int does_not_get_reached = 0;
  if(flag)
  {
    should_not_be_replaced();
    assert(does_not_get_reached);
  }
  should_be_generated();
  return 0;
}

#include <stdio.h>
#include <assert.h>

int param;
void function(int param)
{
  printf("%d\n", param);
  {
    extern int param;
    printf("%d\n", param);
    assert(param == 2);
  }
  assert(param == 1);
}

int main(void)
{
  param = 2;
  function(1);
}

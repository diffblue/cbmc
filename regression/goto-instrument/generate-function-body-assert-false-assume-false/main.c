#include <assert.h>

void crashes_program(void);

int main(void)
{
  int flag;
  if(flag)
  {
    crashes_program();
    assert(0);
  }
  return 0;
}

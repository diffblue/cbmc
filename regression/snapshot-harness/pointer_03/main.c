#include <assert.h>

int x;
void *p;

void initialize()
{
  x = 3;
  p = (void *)&x;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(*(int *)p == 3);

  return 0;
}

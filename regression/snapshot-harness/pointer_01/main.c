#include <assert.h>

int x;
int *p;

void initialize()
{
  x = 3;
  p = &x;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(*p == x);
}

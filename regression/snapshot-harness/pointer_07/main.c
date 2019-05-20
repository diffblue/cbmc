#include <assert.h>
#include <malloc.h>

int *p1;

void initialize()
{
  p1 = malloc(sizeof(int));
  *p1 = 1;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(p1[0] == 1);
  assert(*p1 == 1);
  p1[0] = 2;
  assert(*p1 == 1);
  assert(*p1 != 1);
}

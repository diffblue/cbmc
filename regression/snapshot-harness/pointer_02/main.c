#include <assert.h>
#include <malloc.h>

int x;
int *p1;
int *p2;
int *p3;

void initialize()
{
  x = 3;
  p1 = malloc(sizeof(int));
  p3 = malloc(sizeof(int));
  p2 = &x;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(*p2 == x);
  assert(p1 != p2);
  assert(p1 != p3);
  assert(*p1 == x);
  *p1 = x;
  assert(*p1 == x);
}

#include <assert.h>

int *bar(int *unmodified, int *modifed);

int main()
{
  int x = 3;
  int y = 4;
  int *p2x = &x;
  p2x = bar(&x, &y);
  assert(y == 5);
  assert(p2x == &y);
  assert(*p2x == 5);
}

int *bar(int *unmodified, int *modifed)
{
  assert(*unmodified == 3);

  (*modifed) += 1;

  assert(*modifed == 5);

  return modifed;
}

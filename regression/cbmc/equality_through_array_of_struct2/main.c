#include <assert.h>

#define SIZE 10

struct str
{
  int x;
  int y;
  int z;
};

struct str a[SIZE];

int main (void)
{
  int q;

  for (int i = 0; i < SIZE; ++i)
  {
    a[i].x = q;
  }

  assert(q == a[SIZE - 1].x);

  return 1;
}

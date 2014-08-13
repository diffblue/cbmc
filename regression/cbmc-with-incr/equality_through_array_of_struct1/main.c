#include <assert.h>

#define SIZE 3

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

  a[0].x = q;
  a[1].y = a[0].x;
  a[2].z = a[1].y;

  assert(q == a[2].z);

  return 1;
}

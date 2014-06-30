#include <assert.h>

#define SIZE 21

struct str
{
  int x;
  int y;
  int z;
};

struct str a[SIZE];

int pass_through_array_of_struct (int q)
{
  a[0].x = q;

  for (int i = 1; i < SIZE; ++i)
  {
    switch (i % 3)
    {
    case 1 : a[i].y = a[i-1].x; break;
    case 2 : a[i].z = a[i-1].y; break;
    case 0 : a[i].x = a[i-1].z; break;
    }
  }

  return a[SIZE - 1].z;
}

int main (void)
{
  int q;

  assert(q == pass_through_array_of_struct(q));

  return 1;
}

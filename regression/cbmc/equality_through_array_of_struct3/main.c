#include <assert.h>

#define SIZE 10

struct str
{
  int x;
  int y;
  int z;
};

struct str a[SIZE];

void pass_through_array_of_struct (int q)
{
  for (int i = 0; i < SIZE; ++i)
  {
    a[i].x = q;
  }

  return;
}

int main (void)
{
  int q;

  pass_through_array_of_struct(q);

  assert(q == a[SIZE - 1].x);

  return 1;
}

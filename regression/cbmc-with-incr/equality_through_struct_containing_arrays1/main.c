#include <assert.h>

#define SIZE 4

struct str
{
  int x;
  int y;
  int z;
  int s[SIZE];
  int t[SIZE];
};

struct str s;

void pass_through_struct_containing_arrays (int q)
{
  s.x = q;
  s.y = 0;

  for (int i = 0; i < SIZE; ++i)
  {
    s.s[i] = s.x + s.y;
  }

  for (int i = 0; i < SIZE; ++i)
  {
    s.t[i] = s.s[i];
  }

  return;
}

int main (void)
{
  int q;

  pass_through_struct_containing_arrays(q);

  assert(q == s.t[SIZE - 1] + s.y);

  return 1;
}

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

struct str s[4];

void pass_through_struct_containing_arrays (int q, int j)
{
  s[j].x = j == 0 ? q : s[j - 1].x;
  s[j].y = s[1].z;

  for (int i = 0; i < SIZE; ++i)
  {
    s[j].s[i] = s[j].x + s[j].y;
  }

  for (int i = 0; i < SIZE; ++i)
  {
    s[j].t[i] = s[j].s[i];
  }

  return;
}

int main (void)
{
  int q;

  s[1].z = 0;

  pass_through_struct_containing_arrays(q,0);
  pass_through_struct_containing_arrays(q,1);
  pass_through_struct_containing_arrays(q,2);
  pass_through_struct_containing_arrays(q,3);

  assert(q == s[3].t[SIZE - 1] + s[2].y);

  return 1;
}

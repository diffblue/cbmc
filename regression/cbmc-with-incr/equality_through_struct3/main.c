#include <assert.h>

struct str
{
  int x;
  int y;
  int z;
};

struct str pass_through_struct (int q)
{
  struct str s;

  s.x = q;
  s.y = s.x;
  s.z = s.y;

  return s;
}

int main (void)
{
  int q;

  struct str s = pass_through_struct(q);

  assert(q == s.z);

  return 1;
}

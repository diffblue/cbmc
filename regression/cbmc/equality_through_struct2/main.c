#include <assert.h>

struct str
{
  int x;
  int y;
  int z;
};

int pass_through_struct (int q)
{
  struct str s;

  s.x = q;
  s.y = s.x;
  s.z = s.y;

  return s.z;
}

int main (void)
{
  int q;

  assert(q == pass_through_struct(q));

  return 1;
}

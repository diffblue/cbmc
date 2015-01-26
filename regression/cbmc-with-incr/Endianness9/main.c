#include <assert.h>

int main(void)
{
  // this is yet another gcc extension
  union my_U
  {
    unsigned u;
  } union_object;

  unsigned some_u=10;

  union_object=(union my_U)some_u;
  unsigned u2=union_object.u;

  assert(union_object.u==10);

  return 0;
}

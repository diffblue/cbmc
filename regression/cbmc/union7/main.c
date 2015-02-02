#include <assert.h>

union U
{
  int i : 5;
  int j : 14;
} u;

int main()
{
  assert(sizeof(u)==sizeof(int));
  assert(u.j==0);
  u.i=10;
  int z=u.j;
  assert(z==10<<9); // this assumes big endian
}

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
  assert(u.j==10<<8); // this assumes big endian
}

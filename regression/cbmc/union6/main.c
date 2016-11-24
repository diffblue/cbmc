#include <assert.h>

union U
{
  int i : 5;
  int j : 10;
} u;

int main()
{
  assert(sizeof(u)==sizeof(int));
  assert(u.j==0);
  u.i=10;
  assert(u.j==10); // this assumes little endian
}

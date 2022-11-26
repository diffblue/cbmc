#include <assert.h>

union UNIONNAME
{
  int x1;
  char x3[3];
};

int main()
{
  union UNIONNAME u;
  u.x1 = 0x01010101;

  assert(u.x3[0]);
  assert(u.x3[1]);
  assert(u.x3[2]);

  assert(*((char *)&u.x1));
  assert(*(((char *)&u.x1) + 1));
  assert(*(((char *)&u.x1) + 2));
  char s = *(((char *)&u.x1) + 3);
  assert(s);
  return 0;
}

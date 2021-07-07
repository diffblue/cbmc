#include <assert.h>

void bar(char d[]) __CPROVER_assigns(d[7])
{
}

int main()
{
  char b[10];
  b[0] = 'a';
  b[1] = 'b';
  b[2] = 'c';
  b[3] = 'd';
  b[4] = 'e';
  b[5] = 'f';
  b[6] = 'g';
  b[7] = 'h';
  b[8] = 'i';
  b[9] = 'j';
  bar(b);
  assert(b[7] == 'h');

  return 0;
}

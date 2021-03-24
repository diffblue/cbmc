#include <assert.h>

/* clang-format off */
void foo(char c[]) __CPROVER_assigns(c[2 .. 4])
/* clang-format on */
{
}

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
  foo(b);
  assert(b[0] == 'a');
  assert(b[1] == 'b');
  assert(b[5] == 'f');
  assert(b[6] == 'g');
  assert(b[7] == 'h');
  assert(b[8] == 'i');
  assert(b[9] == 'j');

  b[2] = 'c';
  b[3] = 'd';
  b[4] = 'e';
  bar(b);
  assert(b[0] == 'a');
  assert(b[1] == 'b');
  assert(b[2] == 'c');
  assert(b[3] == 'd');
  assert(b[4] == 'e');
  assert(b[5] == 'f');
  assert(b[6] == 'g');
  assert(b[8] == 'i');
  assert(b[9] == 'j');

  return 0;
}

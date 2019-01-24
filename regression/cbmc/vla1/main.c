#include <assert.h>

int main(int argc, char *argv[])
{
  unsigned char x = argc;
  // make sure int multiplication below won't overflow - type casting to
  // unsigned long long would be possible, but puts yields a challenging problem
  // for the SAT solver
  __CPROVER_assume(x < 1ULL << (sizeof(int) * 8 / 2 - 1));

  struct S
  {
    int a;
    int b[x];
    int c;
  };

  if(x % 2 == 0)
    x = 3;

  struct S s[x];

  __CPROVER_assume(x < 255);
  ++x;

  assert(sizeof(struct S) == ((unsigned char)argc + 2) * sizeof(int));
  assert(sizeof(s) == (x - 1) * ((unsigned char)argc + 2) * sizeof(int));

  return 0;
}

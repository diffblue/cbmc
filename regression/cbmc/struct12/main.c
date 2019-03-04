#include <assert.h>
#include <stdlib.h>

struct S
{
  int a;
  char b[];
};

int main()
{
  struct S *s = malloc(sizeof(struct S) + 1);
  // allocate an object that matches the fixed size of the struct, without the
  // flexible member
  int *p = malloc(sizeof(int));
  s->b[0] = 0;
  assert(s->b[0] == 0);
}

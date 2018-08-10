#include <assert.h>
#include <stdlib.h>

static void f(int *x) { *x = 5; }
static void g(int *x) { assert(*x == 5); }

int main(int argc, char **argv)
{
  int *x = (int*)malloc(sizeof(int));
  f(x);
  g(x);

  return 0;
}

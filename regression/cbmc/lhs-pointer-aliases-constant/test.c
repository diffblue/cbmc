#include <assert.h>

int main(int argc, char **argv)
{
  int x;
  const char *c = "Hello world";

  int *p = (argc ? &x : (int *)c);

  *p = 1;

  assert(*p == 1);

  return 0;
}

#include <assert.h>

unsigned fib(unsigned x)
{
  switch(x)
  {
  case 0:
    return 0;
    break;
  case 1:
    return 1;
    break;
  default:
    return fib(x - 1) + fib(x - 2);
    break;
  }
}

int main(int argc, char **argv)
{
  unsigned v = fib(7);
  assert(v == 13); // Requires context sensitivity to handle with constants

  unsigned w = fib(9);
  assert(w == 24); // Requires location, not just function tracking

  return 0;
}

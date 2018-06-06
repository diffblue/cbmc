#include <assert.h>

int main(int argc, char** argv)
{
  __CPROVER::signedbv<4> x(15);
  __CPROVER::signedbv<4> y;
  y = 13;
  x[1] = 0; //TODO: currently not supported
  assert(x == y);

  return 0;
}

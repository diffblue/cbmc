#include <cassert>

int main(int argc, char** argv)
{
  __CPROVER::signedbv<10> x;
  x = 1;
  __CPROVER::signedbv<10> y = 2;

  __CPROVER::signedbv<10> z = 0;
  z += x;
  z += y;

  __CPROVER::signedbv<10> w = 3;
  assert(z == w);

  return 0;
}

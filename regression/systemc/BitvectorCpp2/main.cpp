#include <cassert>

int main(int argc, char** argv)
{
  __CPROVER::signedbv<4> x(15);
  __CPROVER::signedbv<4> y;
  y = 13;
  x[1] = 0;
  assert(x == y);

  return 0;
}

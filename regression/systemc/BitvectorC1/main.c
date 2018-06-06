#include <assert.h>

#define WIDTH 10

signed __CPROVER_bitvector[WIDTH] add(signed __CPROVER_bitvector[WIDTH] a, signed __CPROVER_bitvector[WIDTH] b)
{
  return a+b;
}

int main(int argc, char** argv)
{
  unsigned __CPROVER_bitvector[WIDTH] x;
  x = 1;
  unsigned __CPROVER_bitvector[WIDTH] y = 2;

  unsigned __CPROVER_bitvector[WIDTH] z = 0;
  z += x;
  z += y;

  unsigned __CPROVER_bitvector[WIDTH] w = 3;
  assert(z == w);

  assert(add(-x,-y) == -w);

  {
    unsigned __CPROVER_bitvector[5] a = 30;
    unsigned __CPROVER_bitvector[3] b;
    unsigned __CPROVER_bitvector[3] c = 6;
    b = a;
    assert(b == c);
  }

  {
    unsigned __CPROVER_bitvector[3] a = 6;
    unsigned __CPROVER_bitvector[5] b;
    unsigned __CPROVER_bitvector[5] c = 6;
    b = a;
    assert(b == c);
  }

  {
    signed __CPROVER_bitvector[5] a = 30;
    signed __CPROVER_bitvector[3] b;
    signed __CPROVER_bitvector[3] c = -2;
    b = a; //just truncated
    assert(b == c);
  }

  {
    signed __CPROVER_bitvector[3] a = -2;
    signed __CPROVER_bitvector[5] b;
    signed __CPROVER_bitvector[5] c = -2;
    b = a; //sign gets extended
    assert(b == c);
  }

  return 0;
}

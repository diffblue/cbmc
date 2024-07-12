#include <complex.h>

int main()
{
  char choice;
  float re = choice ? 1.3f : 2.1f; // a non-constant well-behaved float
  _Complex float z1 = I + re;
  _Complex float z2 = z1 * z1;
  _Complex float expected = 2 * I * re + re * re - 1; // (a+i)^2 = 2ai + a^2 - 1
  _Complex float actual =
    re * re + I; // (a1 + b1*i)*(a2 + b2*i) = (a1*a2 + b1*b2*i)
  __CPROVER_assert(z2 == expected, "right");
  __CPROVER_assert(z2 == actual, "wrong");
  return 0;
}

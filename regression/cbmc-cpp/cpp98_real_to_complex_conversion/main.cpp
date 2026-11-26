extern "C" void __CPROVER_assert(bool, const char *);

#include <complex>

// GNU extension (as C11 6.3.1.7 for C): a real value converts to a complex
// type with an imaginary part of zero; libstdc++'s complex<double> assigns
// its `_Complex double' member from a double
int main()
{
  __complex__ double z;
  z = 4.0;
  __complex__ double w = 3;
  __complex__ float f = 1.5f;
  z += f;
  __CPROVER_assert(
    __real__ z == 5.5 && __imag__ z == 0.0 && __real__ w == 3.0 &&
      __imag__ w == 0.0,
    "real to complex");

  std::complex<double> c(1.0, 2.0);
  c = 4.0;
  __CPROVER_assert(c.real() == 4.0 && c.imag() == 0.0, "std::complex");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

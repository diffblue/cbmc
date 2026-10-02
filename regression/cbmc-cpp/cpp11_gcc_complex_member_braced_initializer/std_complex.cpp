#include <complex>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::complex<float> a(1.0f, 2.0f);
  std::complex<double> b(3.0, 4.0);
  __CPROVER_assert(a.real() == 1.0f && a.imag() == 2.0f, "complex<float>");
  __CPROVER_assert(b.imag() == 4.0, "complex<double>");
  __CPROVER_assert(a.imag() != 2.0f, "WRONG (must FAIL)");
}

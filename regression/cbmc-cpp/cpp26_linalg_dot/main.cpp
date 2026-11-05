// N5008 [linalg.algs.blas1.dot]: dot product.
#include <linalg>
#include <mdspan>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  double a[2] = {1, 2};
  std::mdspan<double, std::extents<int, 2>> v(a);
  __CPROVER_assert(std::linalg::dot(v, v) == 5.0, "dot product");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

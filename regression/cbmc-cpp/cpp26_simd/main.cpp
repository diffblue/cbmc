// N5008 [simd.class]: element-wise addition.
#include <simd>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::simd<int, 4> a(2);
  auto b = a + a;
  __CPROVER_assert(b[0] == 4, "element-wise addition");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

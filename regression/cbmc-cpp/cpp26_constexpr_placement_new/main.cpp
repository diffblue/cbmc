// N5008 [expr.const], [new.delete.placement]: placement new in a constant
// expression.
#include <new>
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int f()
{
  int x = 0;
  int *p = ::new(&x) int(4);
  return *p;
}
template <int V>
struct W
{
  static constexpr int value = V;
};
int main()
{
  __CPROVER_assert(
    W<f()>::value == 4, "placement new in a constant expression");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

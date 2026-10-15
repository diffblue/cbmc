// Negative variant of main.cpp: the condition is false and must be
// diagnosed (N5008 [dcl.pre]/10).
#include <cstddef>
constexpr size_t p2(size_t x)
{
  return size_t(1) << x;
}
constexpr size_t f(size_t e)
{
  return p2(e);
}
static_assert(f(1) == 3, "f(1) is 2");
int main()
{
  return 0;
}

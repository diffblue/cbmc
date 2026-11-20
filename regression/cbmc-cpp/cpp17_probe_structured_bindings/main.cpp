// N5008 [dcl.struct.bind]: a structured binding of a std::pair.
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto [a, b] = std::pair<int, int>(1, 2);
  __CPROVER_assert(a == 1 && b == 2, "structured binding of a pair");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

// N5008 [views.span]: a std::span over an array.
#include <span>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[] = {1, 2, 3};
  std::span<int> s(a);
  __CPROVER_assert(s.size() == 3 && s[1] == 2, "span over an array");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

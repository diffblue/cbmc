// N5008 [unique.ptr.create]: std::make_unique.
#include <memory>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto p = std::make_unique<int>(5);
  __CPROVER_assert(*p == 5, "make_unique");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

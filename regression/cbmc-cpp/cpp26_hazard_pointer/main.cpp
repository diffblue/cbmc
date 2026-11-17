// N5008 [saferecl.hp]: a non-empty hazard pointer.
#include <hazard_pointer>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::hazard_pointer h = std::make_hazard_pointer();
  __CPROVER_assert(!h.empty(), "a non-empty hazard pointer");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

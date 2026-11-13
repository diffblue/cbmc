// N5008 [any]: std::any and any_cast.
#include <any>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::any a = 3;
  __CPROVER_assert(std::any_cast<int>(a) == 3, "any_cast");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

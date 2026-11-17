#include <chrono>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::chrono::seconds s{3};
  __CPROVER_assert(s.count() == 3, "duration");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

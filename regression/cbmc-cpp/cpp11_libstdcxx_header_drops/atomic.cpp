#include <atomic>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::atomic<int> a{1};
  a.fetch_add(1);
  __CPROVER_assert(a.load() == 2, "atomic");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

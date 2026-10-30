#include <stop_token>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::stop_source src;
  __CPROVER_assert(!src.stop_requested(), "stop_source");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

#include <any>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::any a = 42;
  __CPROVER_assert(a.has_value(), "has_value");
  __CPROVER_assert(!a.has_value(), "WRONG (must FAIL)");
}

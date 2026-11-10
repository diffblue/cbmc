// N5008 [expected]: std::expected holding a value and an error.
#include <expected>
extern "C" void __CPROVER_assert(bool, const char *);
std::expected<int, int> f(bool b)
{
  if(b)
    return 1;
  return std::unexpected(2);
}
int main()
{
  __CPROVER_assert(f(true).value() == 1 && f(false).error() == 2, "expected");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

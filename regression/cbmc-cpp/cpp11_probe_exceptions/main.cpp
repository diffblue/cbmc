// N5008 [except.throw], [except.handle]: an exception caught by a handler of
// its base class.
#include <stdexcept>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int r = 0;
  try
  {
    throw std::runtime_error("x");
  }
  catch(const std::exception &)
  {
    r = 1;
  }
  __CPROVER_assert(r == 1, "caught by a base class handler");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

// N5008 [except.spec]/2: in noexcept(constant-expression) the value of the
// expression is the exception specification.  noexcept(sizeof(T) > 100)
// is potentially-throwing for T = int, noexcept(sizeof(T) < 100) is
// non-throwing, and an exception leaving the latter calls std::terminate
// ([except.terminate]/1.3).
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

void handler()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

template <class T>
void non_throwing() noexcept(sizeof(T) < 100)
{
  throw 2;
}

template <class T>
void potentially_throwing() noexcept(sizeof(T) > 100)
{
}

int main()
{
  __CPROVER_assert(
    !noexcept(potentially_throwing<int>()), "noexcept(false expression)");
  std::set_terminate(handler);
  try
  {
    non_throwing<int>();
  }
  catch(int)
  {
  }
  return 0;
}

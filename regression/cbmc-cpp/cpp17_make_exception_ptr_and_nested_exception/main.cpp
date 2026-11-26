// N5008 [propagation]/12: make_exception_ptr(e) refers to a copy of e, as if
// `try { throw e; } catch(...) { return current_exception(); }'.
// [except.nested]/3-4, 8-9: throw_with_nested's exception captures the
// currently handled exception, which rethrow_if_nested throws again.
#include <exception>
#include <stdexcept>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::exception_ptr p = std::make_exception_ptr(42);
  int caught = 0;
  try
  {
    std::rethrow_exception(p);
  }
  catch(int i)
  {
    caught = i;
  }
  __CPROVER_assert(caught == 42, "make_exception_ptr");

  int nested = 0;
  try
  {
    try
    {
      throw 3;
    }
    catch(...)
    {
      std::throw_with_nested(std::runtime_error("outer"));
    }
  }
  catch(const std::exception &e)
  {
    try
    {
      std::rethrow_if_nested(e);
    }
    catch(int i)
    {
      nested = i;
    }
  }
  __CPROVER_assert(nested == 3, "nested exception rethrown");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

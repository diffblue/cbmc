// N5008 [propagation]/7-10: current_exception() in a handler refers to the
// exception object being handled; rethrow_exception(p) throws it again.
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::exception_ptr p;
  try
  {
    throw 42;
  }
  catch(...)
  {
    p = std::current_exception();
  }
  int caught = 0;
  try
  {
    std::rethrow_exception(p);
  }
  catch(int i)
  {
    caught = i;
  }
  __CPROVER_assert(caught == 42, "rethrown");
  __CPROVER_assert(caught == 0, "WRONG (must FAIL)");
}

// N5008 [except.throw]/6: an exception is uncaught from the initialization
// of the exception object until the activation of a handler.
// std::uncaught_exception and std::uncaught_exceptions
// ([uncaught.exceptions]/1) are defined in the compiled library.
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  __CPROVER_assert(!std::uncaught_exception(), "none before the throw");
  try
  {
    throw 1;
  }
  catch(int)
  {
    __CPROVER_assert(!std::uncaught_exception(), "none in the handler");
  }
  __CPROVER_assert(std::uncaught_exceptions() == 0, "count after");
  __CPROVER_assert(std::uncaught_exceptions() == 1, "WRONG (must FAIL)");
  return 0;
}

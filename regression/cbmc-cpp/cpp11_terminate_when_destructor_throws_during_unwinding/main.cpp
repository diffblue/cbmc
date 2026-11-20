// N5008 [except.terminate]/1.4, /2: when the destruction of an object
// during stack unwinding exits via an exception, std::terminate is called,
// which calls the terminate handler ([terminate.handler]).  The handler
// below asserts; a verifier that assumes the destructor does not throw
// misses that failure.
#include <cstdlib>
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

bool unwinding = false;

void handler()
{
  __CPROVER_assert(unwinding, "terminate called from the unwinding");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  std::abort();
}

struct T
{
  ~T() noexcept(false)
  {
    if(unwinding)
      throw 2;
  }
};

int main()
{
  std::set_terminate(handler);
  try
  {
    T t;
    unwinding = true;
    throw 1;
  }
  catch(...)
  {
  }
  return 0;
}

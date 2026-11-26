// N5008 [except.spec]/3, /7: a destructor without a noexcept-specifier has
// a non-throwing exception specification unless a destructor of a
// potentially constructed subobject is potentially-throwing; an exception
// leaving it calls std::terminate ([except.terminate]/1.3), which calls the
// handler of std::set_terminate.
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

void handler()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

struct T
{
  ~T()
  {
    throw 1;
  }
};

int main()
{
  std::set_terminate(handler);
  try
  {
    T t;
  }
  catch(int)
  {
  }
  return 0;
}

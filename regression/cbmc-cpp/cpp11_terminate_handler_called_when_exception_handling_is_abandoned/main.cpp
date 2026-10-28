// N5008 [except.terminate]/1-2: std::terminate is called when no handler is
// found for an exception (1.2; [except.handle]/9) and when the search for
// a handler leaves a function with a non-throwing exception specification
// (1.3); a program may also call it directly ([terminate]/2).  It calls the
// handler installed by std::set_terminate ([terminate]/1,
// [set.terminate]/1).  [except.spec]/2: noexcept(false) is
// potentially-throwing; throw() is non-throwing (C++11 [except.spec]/12).
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" int nondet_int();

#ifdef WHICH
int which = WHICH;
#else
int which = nondet_int();
#endif

void handler()
{
  __CPROVER_assert(which >= 1 && which <= 3, "handler only on these paths");
  __CPROVER_assert(which != 1, "terminate: exception leaves main");
  __CPROVER_assert(which != 2, "terminate: exception leaves noexcept");
  __CPROVER_assert(which != 3, "terminate: called directly");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

void non_throwing() noexcept
{
  throw 2;
}

void potentially_throwing() noexcept(false)
{
  throw 0;
}

void old_style() throw()
{
}

int main()
{
  std::set_terminate(handler);
  __CPROVER_assert(std::get_terminate() == handler, "handler installed");
  __CPROVER_assert(noexcept(old_style()), "throw() is non-throwing");
  if(which == 1)
    throw 1;
  if(which == 2)
    non_throwing();
  if(which == 3)
    std::terminate();
  try
  {
    potentially_throwing();
  }
  catch(int)
  {
  }
  return 0;
}

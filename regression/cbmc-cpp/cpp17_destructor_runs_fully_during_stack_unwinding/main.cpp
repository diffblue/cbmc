// N5008 [except.ctor]/1-2: stack unwinding destroys the automatic objects
// constructed since the try block was entered; each destructor runs its
// whole body.  [except.throw]/6, Note 4: the exception is uncaught during
// the stack unwinding, so std::uncaught_exceptions() ([uncaught.exceptions]
// /1) is 1 in such a destructor.  An exception thrown and caught inside the
// destructor does not affect the one being unwound.
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

int steps = 0;
int count_in_destructor = -1;
bool inner_caught = false;

void step()
{
  ++steps;
}

struct D
{
  ~D()
  {
    step();
    count_in_destructor = std::uncaught_exceptions();
    try
    {
      throw 'c';
    }
    catch(char)
    {
      inner_caught = true;
    }
    ++steps;
  }
};

void f()
{
  D d;
  throw 1;
}

int main()
{
  int caught = 0;
  try
  {
    f();
  }
  catch(int x)
  {
    caught = x;
  }
  __CPROVER_assert(steps == 2, "destructor body completes");
  __CPROVER_assert(count_in_destructor == 1, "one uncaught exception");
  __CPROVER_assert(inner_caught, "inner exception caught");
  __CPROVER_assert(caught == 1, "outer exception caught");
  __CPROVER_assert(std::uncaught_exceptions() == 0, "none after the handler");
  __CPROVER_assert(steps == 1, "WRONG (must FAIL)");
  return 0;
}

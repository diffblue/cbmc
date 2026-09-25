// N5008 [except.throw]/4: when an exception is thrown, control is transferred
// to the nearest matching handler, unwinding the call stack -- so an exception
// thrown in a callee is caught by a handler in a (transitive) caller, with the
// handler parameter initialized from the exception object.
//
// Cross-function regression test for the goto-level C++ exception lowering
// (remove_cpp_exceptions, built on the shared remove_exceptions_baset): the
// throw in deep() propagates through mid() (which has no handler) to main()'s
// catch(Base &), matching by base class, with the thrown value carried across
// the returns.
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct Base
{
  int code;
  Base(int c) : code(c)
  {
  }
};

struct Derived : Base
{
  Derived(int c) : Base(c)
  {
  }
};

static void deep()
{
  throw Derived(42);
}

static void mid()
{
  deep(); // no handler here: the exception propagates through
}

int main()
{
  try
  {
    mid();
  }
  catch(Base &b)
  {
    __CPROVER_assert(
      b.code == 42, "cross-function base handler sees the thrown value");
    __CPROVER_assert(b.code != 42, "WRONG must FAIL");
  }
  return 0;
}

// N5008 [except.throw]/8: a throw-expression with no operand (`throw;`)
// rethrows the exception currently being handled; the same exception object
// propagates to the next enclosing handler.
//
// Regression test for rethrow lowering (remove_cpp_exceptions re-propagates the
// saved current exception instead of constructing a new object).  The inner
// handler rethrows; the outer handler must see the same exception value.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct E
{
  int c;
  E(int x) : c(x)
  {
  }
};

static void f()
{
  throw E(9);
}

int main()
{
  int stage = 0;
  try
  {
    try
    {
      f();
    }
    catch(E &e)
    {
      stage = 1;
      throw; // rethrow the exception being handled
    }
  }
  catch(E &e)
  {
    stage = 2;
    __CPROVER_assert(e.c == 9, "rethrown exception value preserved");
    __CPROVER_assert(stage == 2, "outer handler reached after rethrow");
    __CPROVER_assert(e.c != 9, "WRONG must FAIL");
  }
  return 0;
}

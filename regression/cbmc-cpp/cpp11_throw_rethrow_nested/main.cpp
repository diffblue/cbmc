// N5008 [except.throw]/8: a `throw;` with no operand rethrows the exception
// currently being handled -- i.e. the exception of the handler it (dynamically)
// appears in.  Here the outer handler is handling E(1); it enters and completes
// an inner try/catch handling E(2), then executes `throw;`, which must rethrow
// E(1) (the exception the outer handler is handling), not E(2).
//
// KNOWNBUG: remove_cpp_exceptions tracks the exception being handled in a single
// pair of "current exception" globals rather than a stack.  Entering the inner
// handler overwrites them with E(2) and does not restore E(1) on exit, so the
// outer `throw;` re-propagates E(2).  Assertion 2 currently FAILS.  Flip to CORE
// once the current-exception state is maintained as a stack across nested
// handlers.

extern "C" void __CPROVER_assert(int, const char *);

struct E
{
  int c;
  E(int x) : c(x)
  {
  }
};

int main()
{
  int reached = 0;
  try
  {
    try
    {
      throw E(1);
    }
    catch(E &outer)
    {
      try
      {
        throw E(2);
      }
      catch(E &inner)
      {
      }
      throw; // must rethrow E(1), the exception the outer handler is handling
    }
  }
  catch(E &e)
  {
    reached = 1;
    __CPROVER_assert(reached == 1, "outer handler reached after rethrow");
    __CPROVER_assert(
      e.c == 1, "outer rethrow re-propagates the outer exception E(1)");
  }
  return 0;
}

// N5008 [except.ctor]/1-3, [except.throw]/4: as an exception propagates to the
// handler that catches it, every automatic object whose scope is exited during
// the unwinding is destroyed.  Here B is thrown in f(); the inner `try` catches
// only A, so B propagates out of the inner try to the outer `catch(B&)`.  The
// object `g`, constructed in the outer try before the inner try, has its scope
// exited during this unwinding and must be destroyed before the outer handler
// runs.
//
// KNOWNBUG: the goto-conversion destructor-unwinding only unwinds up to the
// innermost enclosing try at the point of the throw (and the throw here is in
// f(), which has no enclosing try, so only f()'s own locals are unwound).
// Objects in an outer scope that is exited only because the exception fails to
// match an inner handler are not destroyed, so `g`'s destructor never runs and
// assertion 2 fails.  Flip to CORE once unwinding runs the destructors of every
// scope exited on the way to the matching handler.

extern "C" void __CPROVER_assert(int, const char *);

static int destroyed = 0;
static int reached = 0;

struct G
{
  ~G()
  {
    destroyed = 1;
  }
};

struct A
{
};
struct B
{
};

static void f()
{
  throw B();
}

int main()
{
  try
  {
    G g;
    try
    {
      f();
    }
    catch(A &)
    {
    }
  }
  catch(B &)
  {
    reached = 1;
    __CPROVER_assert(reached == 1, "outer B handler reached");
    __CPROVER_assert(
      destroyed == 1, "outer-try object destroyed during unwinding");
  }
  return 0;
}

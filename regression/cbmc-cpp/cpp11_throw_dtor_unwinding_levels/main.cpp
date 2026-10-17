// N5008 [except.ctor]/1-3: as an exception propagates to the handler that
// catches it, every automatic object whose scope is exited during the
// unwinding is destroyed -- and only those.  Level-by-level cases (verified
// against g++ and clang++):
//  1. three nested tries, exception caught two levels up: both intervening
//     objects destroyed, innermost first;
//  2. inner handler matches: the enclosing-scope object is NOT destroyed
//     before the handler runs, and is destroyed exactly once in total;
//  3. rethrow from an inner handler: the enclosing-scope object is live in the
//     handler and destroyed before the outer handler runs.

extern "C" void __CPROVER_assert(int, const char *);

static int order[2];
static int n = 0;

struct G0
{
  ~G0()
  {
    order[n++] = 0;
  }
};

struct G1
{
  ~G1()
  {
    order[n++] = 1;
  }
};

struct A
{
};
struct B
{
};
struct C
{
};

static void f()
{
  throw C();
}

static void three_levels()
{
  try
  {
    G0 g0;
    try
    {
      G1 g1;
      try
      {
        f();
      }
      catch(A &)
      {
        __CPROVER_assert(0, "A handler unreachable");
      }
    }
    catch(B &)
    {
      __CPROVER_assert(0, "B handler unreachable");
    }
  }
  catch(C &)
  {
    __CPROVER_assert(n == 2, "both intervening objects destroyed");
    __CPROVER_assert(
      order[0] == 1 && order[1] == 0, "inner g1 destroyed before outer g0");
  }
}

static int destroyed = 0;

struct G
{
  ~G()
  {
    ++destroyed;
  }
};

static void inner_handler_matches()
{
  destroyed = 0;
  try
  {
    G g;
    try
    {
      throw A();
    }
    catch(A &)
    {
      __CPROVER_assert(destroyed == 0, "g live in the matching inner handler");
    }
  }
  catch(...)
  {
    __CPROVER_assert(0, "outer handler unreachable");
  }
  __CPROVER_assert(destroyed == 1, "g destroyed exactly once in total");
}

static void rethrow_unwinds()
{
  destroyed = 0;
  try
  {
    G g;
    try
    {
      throw B();
    }
    catch(B &)
    {
      __CPROVER_assert(destroyed == 0, "g live in the rethrowing handler");
      throw;
    }
  }
  catch(B &)
  {
    __CPROVER_assert(destroyed == 1, "g destroyed before the outer handler");
  }
}

int main()
{
  three_levels();
  inner_handler_matches();
  rethrow_unwinds();
  return 0;
}

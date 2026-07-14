// N5008 [except.ctor]/1-3, [except.throw]/4: every automatic object whose
// scope is exited while an exception propagates to its handler is destroyed.
// Two related call-site cases (cross-checked against g++ and clang++, which
// destroy both objects):
//   g1: constructed inside the try, before a call that throws -- its scope is
//       exited when control passes to the handler, so it must be destroyed;
//   g2: a local of an intermediate function (no try) through which the
//       exception propagates -- destroyed as that function unwinds.
//
// KNOWNBUG: destructor-unwinding is emitted only at throw sites (up to the
// innermost enclosing try of the *throwing* function).  The exceptional edge
// at a *call site* runs no destructors: objects constructed between the try
// entry and the call (g1), and locals of intermediate functions without a try
// (g2), are never destroyed.  Fixing this needs a guarded unwind block after
// possibly-throwing calls (from the call's scope down to the innermost try),
// coordinated between goto conversion and the exception-lowering pass.  Flip
// to CORE once call-site unwinding runs these destructors.

extern "C" void __CPROVER_assert(int, const char *);

static int destroyed = 0;

struct G
{
  ~G()
  {
    ++destroyed;
  }
};

struct B
{
};

static void thrower()
{
  throw B();
}

static void intermediate()
{
  G g2;
  thrower();
}

int main()
{
  try
  {
    G g1;
    intermediate();
  }
  catch(B &)
  {
    __CPROVER_assert(destroyed == 2, "g1 and g2 destroyed during unwinding");
  }
  return 0;
}

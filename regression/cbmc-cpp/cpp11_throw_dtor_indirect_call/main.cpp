// N5008 [except.ctor]/1-3: automatic objects whose scope is exited during
// unwinding are destroyed regardless of HOW the throwing callee was invoked.
// The call-site unwind cleanup is attached to the CALL instruction by the
// goto conversion; function-pointer removal and virtual-function removal
// rewrite such a call into a dispatch chain of concrete calls, and must carry
// the cleanup association onto them -- otherwise the exception lowering adds
// its own dispatch after each concrete call, jumping to a handler before the
// destructors run.  Covers a virtual call, a function-pointer call, and a
// loop-scoped object with a throwing callee.  Runtime-verified against g++
// and clang++.

extern "C" void __CPROVER_assert(int, const char *);

static int destroyed = 0;
static int calls = 0;

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

struct Base
{
  virtual void f()
  {
    throw B();
  }
  virtual ~Base()
  {
  }
};

struct Der : Base
{
  void f() override
  {
    throw B();
  }
};

static void thrower()
{
  throw B();
}

static void maybe_throw()
{
  if(++calls == 2)
    throw B();
}

int main()
{
  destroyed = 0;
  Der d;
  Base *p = &d;
  try
  {
    G g;
    p->f();
  }
  catch(B &)
  {
    __CPROVER_assert(destroyed == 1, "destroyed across a virtual call");
  }

  destroyed = 0;
  void (*fp)() = thrower;
  try
  {
    G g;
    fp();
  }
  catch(B &)
  {
    __CPROVER_assert(destroyed == 1, "destroyed across a function-pointer call");
  }

  destroyed = 0;
  try
  {
    for(int i = 0; i < 3; ++i)
    {
      G g;
      maybe_throw();
    }
  }
  catch(B &)
  {
    __CPROVER_assert(
      destroyed == 2, "loop: one normal-exit + one unwinding destruction");
  }
  return 0;
}

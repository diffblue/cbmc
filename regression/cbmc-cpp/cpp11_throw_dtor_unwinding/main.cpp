// N5008 [except.ctor]/1-3, [except.throw]/4: when an exception is thrown, the
// automatic objects constructed since entering the try block are destroyed, in
// reverse order of construction, as the stack unwinds to the handler.
//
// Regression test for running destructors during C++ stack unwinding
// (goto-conversion emits the unwinding destructors before the THROW).  Two
// guard objects are constructed in the try; the throw must run both
// destructors exactly once, B before A, and must NOT destroy the object
// declared before the try.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

static int order = 0;
static int count_a = 0;
static int count_b = 0;
static int outer_destroyed = 0;

struct A
{
  ~A()
  {
    count_a++;
    if(order == 0)
      order = 1; // A destroyed first would set order to 1
  }
};

struct B
{
  ~B()
  {
    count_b++;
    if(order == 0)
      order = 2; // B destroyed first sets order to 2 (expected: reverse order)
  }
};

struct Outer
{
  ~Outer()
  {
    outer_destroyed++;
  }
};

int main()
{
  Outer o; // constructed before the try: must survive into the handler
  try
  {
    A a;
    B b;
    throw 1;
  }
  catch(int)
  {
    __CPROVER_assert(
      count_a == 1 && count_b == 1, "both destructors ran exactly once");
    __CPROVER_assert(order == 2, "destroyed in reverse order: B before A");
    __CPROVER_assert(
      outer_destroyed == 0, "object declared before the try not yet destroyed");
    __CPROVER_assert(count_a != 1, "WRONG must FAIL");
  }
  return 0;
}

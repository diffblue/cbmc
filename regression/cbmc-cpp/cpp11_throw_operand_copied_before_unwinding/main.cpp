// N5008 [expr.throw]/2: the exception object is copy-initialized from the
// operand; [except.ctor]/1-2: stack unwinding then destroys the automatic
// objects constructed since the try block was entered.  An operand that
// names such an object is read before it is destroyed.
extern "C" void __CPROVER_assert(bool, const char *);

struct D
{
  int v = 5;
  D() = default;
  D(const D &o) : v(o.v)
  {
  }
  ~D()
  {
    v = 0;
  }
};

int main()
{
  int scalar = -1;
  try
  {
    D d;
    throw d.v;
  }
  catch(int x)
  {
    scalar = x;
  }
  __CPROVER_assert(scalar == 5, "member of a local thrown");

  int member = -1;
  try
  {
    D d;
    throw d;
  }
  catch(const D &x)
  {
    member = x.v;
  }
  __CPROVER_assert(member == 5, "local object thrown");
  __CPROVER_assert(member == 0, "WRONG (must FAIL)");
  return 0;
}

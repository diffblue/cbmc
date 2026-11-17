// N5008 [expr.throw]/2: the exception object is copy-initialized from the
// operand, so the copy constructor of a class type runs.
// [class.copy.elision]/1.2 does not allow omitting this copy: the scope of
// `e' extends beyond the innermost enclosing try block.
extern "C" void __CPROVER_assert(bool, const char *);

int copies = 0;

struct E
{
  bool copied = false;
  E() = default;
  E(const E &) : copied(true)
  {
    ++copies;
  }
};

int main()
{
  E e;
  bool handler_sees_copy = false;
  try
  {
    throw e;
  }
  catch(const E &x)
  {
    handler_sees_copy = x.copied;
  }
  __CPROVER_assert(copies == 1, "copy constructor ran once");
  __CPROVER_assert(handler_sees_copy, "handler binds to the copy");
  __CPROVER_assert(copies == 0, "WRONG (must FAIL)");
  return 0;
}

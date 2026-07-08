// N5008 [except.handle]/3: a handler `catch(B &)` matches a thrown object of a
// type publicly derived from B, and the handler parameter is bound to the
// (base subobject of the) exception object.  So `throw Derived(9)` caught by
// `catch(Base &b)` enters the handler with b.code == 9.
//
// The goto-level C++ exception lowering matches handlers via the thrown type's
// exception-id set, which includes base classes (cpp_exception_list), so
// base-class matching and the value binding both work.
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

int main()
{
  try
  {
    throw Derived(9);
  }
  catch(Base &b)
  {
    __CPROVER_assert(b.code == 9, "base handler catches derived, value bound");
    __CPROVER_assert(b.code != 9, "WRONG must FAIL");
  }
  return 0;
}

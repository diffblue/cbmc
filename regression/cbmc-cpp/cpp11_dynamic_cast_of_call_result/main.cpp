// N5008 [expr.dynamic.cast]/6-10: the run-time check applies to any operand,
// also to one with side effects, which is evaluated once.  libc++'s
// rethrow_if_nested casts `std::addressof(e)' across to nested_exception.
// <typeinfo> declares std::bad_cast, which a failed reference cast throws.
#include <typeinfo>
extern "C" void __CPROVER_assert(bool, const char *);

struct Ex
{
  virtual ~Ex()
  {
  }
  int e = 1;
};
struct RT : Ex
{
  int r = 2;
};
struct NE
{
  virtual ~NE()
  {
  }
  int p = 42;
};
struct Nested : RT, NE
{
};

int calls = 0;
Nested obj;
Ex *get()
{
  ++calls;
  return &obj;
}
Ex &get_ref()
{
  ++calls;
  return obj;
}

int main()
{
  NE *n = dynamic_cast<NE *>(get());
  __CPROVER_assert(n && n->p == 42 && calls == 1, "cross cast, one call");
  RT *r = dynamic_cast<RT *>(get());
  __CPROVER_assert(r && r->r == 2 && calls == 2, "downcast, one call");
  void *v = dynamic_cast<void *>(get());
  __CPROVER_assert(v == &obj && calls == 3, "to void *, one call");
  NE &nr = dynamic_cast<NE &>(get_ref());
  __CPROVER_assert(nr.p == 42 && calls == 4, "reference cross cast, one call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// Returning a std::pair (or any class) by value move-constructs the result via
// the defaulted move constructor pair(pair&&)=default.  CBMC generates the body
// of an explicitly-defaulted copy/move constructor as the memberwise
// copy/move ([class.copy.ctor]/14).  This must be done for the *move*
// constructor (rvalue-reference parameter), not only the copy constructor, and
// for class-typed members (not only scalars); otherwise the returned pair is
// left nondet.  Regression test for that fix.
#include <utility>

struct Ptr
{
  int *p;
  Ptr() : p(0)
  {
  }
  explicit Ptr(int *q) : p(q)
  {
  }
  // copy/move constructors are implicit
};

std::pair<Ptr, Ptr> make_it(int *a, int *b)
{
  return std::pair<Ptr, Ptr>(Ptr(a), Ptr(b)); // prvalue, returned by value
}

int main()
{
  int u, v;

  // Direct construction (no return) -- worked before the fix.
  std::pair<Ptr, Ptr> d(Ptr(&u), Ptr(&v));
  __CPROVER_assert(d.first.p == &u, "direct construction preserves members");

  // Explicit move construction.
  std::pair<Ptr, Ptr> m(static_cast<std::pair<Ptr, Ptr> &&>(d));
  __CPROVER_assert(m.first.p == &u, "move constructor preserves members");

  // Explicit copy construction.
  std::pair<Ptr, Ptr> c(d);
  __CPROVER_assert(c.first.p == &u, "copy constructor preserves members");

  // Returned by value (move-constructed at the call site).
  std::pair<Ptr, Ptr> r = make_it(&u, &v);
  __CPROVER_assert(r.first.p == &u, "by-value return preserves .first");
  __CPROVER_assert(r.second.p == &v, "by-value return preserves .second");

  // std::make_pair returns by value too.
  std::pair<Ptr, Ptr> q = std::make_pair(Ptr(&u), Ptr(&v));
  __CPROVER_assert(q.first.p == &u, "make_pair preserves .first");
  return 0;
}

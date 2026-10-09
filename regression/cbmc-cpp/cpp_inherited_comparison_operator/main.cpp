// A comparison operator (operator==, operator<, ...) declared as a member
// of a base class is a member candidate when comparing objects of a
// derived class: the qualified lookup of `Derived::operator@`
// ([over.match.oper]/3.2) finds members inherited from base classes
// ([class.member.lookup]).  These comparisons must resolve to the
// inherited operator, not fall back to a (non-existent) built-in
// conversion of the class to bool.

#include <cassert>

struct base
{
  int v;
  explicit base(int x) : v(x)
  {
  }
  bool operator==(const base &o) const
  {
    return v == o.v;
  }
  bool operator<(const base &o) const
  {
    return v < o.v;
  }
};

struct derived : base
{
  explicit derived(int x) : base(x)
  {
  }
};

int main()
{
  derived a(1), b(2);
  assert(a == a);
  assert(!(a == b));
  assert(a < b);
  assert(!(b < a));
  return 0;
}

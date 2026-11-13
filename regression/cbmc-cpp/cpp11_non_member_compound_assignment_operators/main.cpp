extern "C" void __CPROVER_assert(bool, const char *);
#include <list>
// N5008 [over.match.oper]/3: for `a @= b` with a class-type left operand the
// candidates include the NON-MEMBER operator@= found by unqualified lookup
// (and ADL), not only T1::operator@=.
struct V
{
  int v;
};
V &operator+=(V &a, const V &b)
{
  a.v += b.v;
  return a;
}
V &operator-=(V &a, const V &b)
{
  a.v -= b.v;
  return a;
}
V &operator*=(V &a, const V &b)
{
  a.v *= b.v;
  return a;
}
V &operator/=(V &a, const V &b)
{
  a.v /= b.v;
  return a;
}
V &operator%=(V &a, const V &b)
{
  a.v %= b.v;
  return a;
}
V &operator&=(V &a, const V &b)
{
  a.v &= b.v;
  return a;
}
V &operator|=(V &a, const V &b)
{
  a.v |= b.v;
  return a;
}
V &operator^=(V &a, const V &b)
{
  a.v ^= b.v;
  return a;
}
V &operator<<=(V &a, const V &b)
{
  a.v <<= b.v;
  return a;
}
V &operator>>=(V &a, const V &b)
{
  a.v >>= b.v;
  return a;
}
// friend declared in-class, defined out of line (CBMC's guard_exprt shape)
class guard_exprt
{
public:
  explicit guard_exprt(int e) : expr(e)
  {
  }
  int get() const
  {
    return expr;
  }
  friend guard_exprt &operator|=(guard_exprt &g1, const guard_exprt &g2);

private:
  int expr;
};
using guardt = guard_exprt;
guard_exprt &operator|=(guard_exprt &g1, const guard_exprt &g2)
{
  g1.expr |= g2.expr;
  return g1;
}
// a member operator must still win when present
struct M
{
  int v;
  M &operator|=(const M &o)
  {
    v |= o.v;
    return *this;
  }
};
V &operator|=(V &a, const M &m)
{
  a.v |= m.v;
  return a;
}
int main()
{
  V a{6}, b{3};
  a += b;
  __CPROVER_assert(a.v == 9, "+=");
  a -= b;
  __CPROVER_assert(a.v == 6, "-=");
  a *= b;
  __CPROVER_assert(a.v == 18, "*=");
  a /= b;
  __CPROVER_assert(a.v == 6, "/=");
  a %= V{4};
  __CPROVER_assert(a.v == 2, "%=");
  a |= V{4};
  __CPROVER_assert(a.v == 6, "|=");
  a &= V{3};
  __CPROVER_assert(a.v == 2, "&=");
  a ^= V{1};
  __CPROVER_assert(a.v == 3, "^=");
  a <<= V{2};
  __CPROVER_assert(a.v == 12, "<<=");
  a >>= V{1};
  __CPROVER_assert(a.v == 6, ">>=");
  std::list<guardt> l{guardt(1), guardt(2), guardt(4)};
  guardt read_guard(l.front());
  for(std::list<guardt>::const_iterator it = ++(l.begin()); it != l.end(); ++it)
    read_guard |= *it;
  __CPROVER_assert(
    read_guard.get() == 7,
    "friend operator|= over a const_iterator dereference");
  M m1{1}, m2{2};
  m1 |= m2;
  __CPROVER_assert(m1.v == 3, "member operator|= still used");
  V c{8};
  c |= m1;
  __CPROVER_assert(
    c.v == 11, "non-member operator|= with a different right operand type");
  return 0;
}

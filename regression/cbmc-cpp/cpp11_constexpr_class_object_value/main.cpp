// N5008 [dcl.constexpr]/1, /6 and [expr.const]: a constexpr object of class
// type is a const object usable in constant expressions -- its members and
// its constexpr member functions can be read in a static_assert -- and it is
// an object at run time.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int v = 3;
  constexpr int n() const
  {
    return 5;
  }
  constexpr int twice() const
  {
    return 2 * v;
  }
};
struct P
{
  int v;
  int w = 7;
  constexpr P(int x) : v(x)
  {
  }
  constexpr P() : v(1)
  {
  }
};

constexpr S g;
constexpr P gp(42);
constexpr P gq = P();
static_assert(g.v == 3 && g.n() == 5 && g.twice() == 6, "namespace scope S");
static_assert(gp.v == 42 && gp.w == 7, "namespace scope P(42)");
static_assert(gq.v == 1 && gq.w == 7, "namespace scope P()");

int main()
{
  constexpr S s;
  constexpr S t{};
  constexpr S u = S();
  constexpr P p(42);
  constexpr P q = P();
  constexpr P r{5};
  static_assert(s.v == 3 && s.n() == 5 && s.twice() == 6, "block: S");
  static_assert(t.twice() == 6 && u.twice() == 6, "block: S{} and S()");
  static_assert(p.v == 42 && p.w == 7, "block: P(42)");
  static_assert(q.v == 1 && q.w == 7, "block: P()");
  static_assert(r.v == 5 && r.w == 7, "block: P{5}");
  // the objects exist at run time with the same values
  __CPROVER_assert(g.v == 3 && gp.v == 42 && gq.w == 7, "namespace objects");
  __CPROVER_assert(s.v == 3 && p.v == 42 && q.v == 1, "local objects");
  __CPROVER_assert(g.n() == 5 && p.w == 7, "member call and member");
  // N5008 [basic.def.odr], [dcl.constexpr]/6: a constexpr object is a const
  // object -- its address can be taken and it binds to a reference
  const S *ptr = &g;
  const P &ref = gp;
  __CPROVER_assert(ptr->twice() == 6 && ref.v == 42, "through pointer/ref");
  __CPROVER_assert(&ref == &gp && ptr == &g, "address identity");
  __CPROVER_assert(gp.w == 8, "WRONG (must FAIL)");
  return 0;
}

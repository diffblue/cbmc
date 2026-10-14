// N5008 [dcl.init.ref]/5.4.1: when the referenced type is reference-related
// to the initializer's type, cv1 shall be at least as cv-qualified as cv2,
// so `E &&' does not bind to a `const E' prvalue (not even by copying it
// into a temporary): `push_back(c ? neg(op) : op)' with `const E &op' -- a
// `const E' prvalue by [expr.cond]/4.3 -- selects push_back(const E &); it
// was ambiguous (CBMC's own goto_check_c.cpp, expr2c.cpp, dog-fooding).
// [expr.type.conv]/2, [over.ics.rank]/3.2.3: the aggregate prvalue `E{2}'
// binds to `E &&' by the identity conversion, which beats `const E &'; the
// front end's compound literal was taken for an lvalue and the rvalue
// reference binding ranked as a copy.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
  int v;
};
struct C
{
  int v;
  C(int x) : v(x)
  {
  }
};
int pb(const E &e)
{
  return 1;
}
int pb(E &&e)
{
  return 2;
}
int pc(const C &e)
{
  return 1;
}
int pc(C &&e)
{
  return 2;
}
E neg(const E &e)
{
  return E{-e.v};
}
const E cneg(const E &e)
{
  return E{-e.v};
}
E mk()
{
  return E{1};
}
int f(const E &op, bool c)
{
  return pb(
    c ? neg(op) : op); // E1 prvalue E, E2 lvalue const E: const E prvalue
}
int g(E &op, bool c)
{
  return pb(c ? neg(op) : op); // E1 prvalue E, E2 lvalue E: E prvalue
}
int main()
{
  E a{1};
  C c(1);
  __CPROVER_assert(
    f(a, true) == 1 && f(a, false) == 1, "const E prvalue binds const E&");
  __CPROVER_assert(g(a, true) == 2 && g(a, false) == 2, "E prvalue binds E&&");
  __CPROVER_assert(pb(cneg(a)) == 1, "const call result binds const E&");
  __CPROVER_assert(pb(E{2}) == 2, "aggregate braced prvalue binds E&&");
  __CPROVER_assert(pb(mk()) == 2, "call prvalue binds E&&");
  __CPROVER_assert(pb(a) == 1, "lvalue binds const E&");
  __CPROVER_assert(pc(C{2}) == 2 && pc(C(3)) == 2, "class prvalues bind C&&");
  __CPROVER_assert(pc(c) == 1, "class lvalue binds const C&");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

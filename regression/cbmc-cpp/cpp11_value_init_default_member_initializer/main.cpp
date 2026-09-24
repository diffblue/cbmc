// N5008 [expr.type.conv]/2 + [dcl.init.general]/9.1: `T()` value-initializes
// -- zero-initialization, then default-initialization when T's default
// constructor is non-trivial; a default member initializer makes the implicit
// default constructor non-trivial ([class.default.ctor]/3).
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int v = 3;
  int w = 4;
};
struct R
{
  int v = 3;
  int w; // zero-initialized by value-initialization
};
struct P
{
  int v = 3;
  constexpr P()
  {
  }
};
struct B
{
  int b = 9;
};
struct D : B
{
  int d = 8;
};

int main()
{
  S a;
  S b{};
  S c = S();
  S d = S{};
  R r = R();
  P p = P();
  D dd = D();
  __CPROVER_assert(a.v == 3 && a.w == 4, "default-initialization");
  __CPROVER_assert(b.v == 3 && b.w == 4, "braced");
  __CPROVER_assert(c.v == 3 && c.w == 4, "S()");
  __CPROVER_assert(d.v == 3 && d.w == 4, "S{}");
  __CPROVER_assert(r.v == 3 && r.w == 0, "R(): initializer and zero");
  __CPROVER_assert(p.v == 3, "P(): user-provided constructor");
  __CPROVER_assert(dd.b == 9 && dd.d == 8, "D(): base's initializer");
  __CPROVER_assert(S().v + R().w == 3, "temporaries");
  __CPROVER_assert(c.v == 0, "WRONG (must FAIL)");
  return 0;
}

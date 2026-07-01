// N5008 [expr.prim.lambda.general]/4: a lambda is generic only if it has an
// explicit template-parameter-list or a parameter of type auto.  A lambda
// parameter written with an ordinary (concrete) class name -- e.g. `E &` -- is
// NOT a generic/template parameter and must be type-checked as that class type.
//
// Regression: CBMC treated any lambda parameter whose type is a bare name
// (cpp_name) as a generic `auto` parameter and replaced it with `signed int`,
// so a lambda that accessed a member of a class-typed parameter failed with
// "member operator requires struct/union type ... but got 'signed int'", and
// the enclosing function's body was dropped.  This is exactly what stubbed
// util/expr.cpp's `exprt::visit` to a no-op (`exprt::visit(v)` calls
// `visit_pre([&v](exprt &e){ v(e); })`), which would silently make any analysis
// using exprt::visit run vacuously.
//
// Here a captureless lambda with a class-reference parameter mutates the
// referent (must run: e.v==7), and a by-value class parameter reads a member
// (must be the concrete type, not int).  g++/clang++ agree.  assertion.3 must
// FAIL, proving non-vacuity.

extern "C" void __CPROVER_assert(int, const char *);

struct E
{
  int v;
  int w;
};

int main()
{
  E e;
  e.v = 0;
  e.w = 3;

  auto by_ref = [](E &x) { x.v = 7; };
  by_ref(e);

  int seen = 0;
  auto by_val = [&seen](E x) { seen = x.w; };
  by_val(e);

  __CPROVER_assert(e.v == 7, "lambda with class-reference parameter runs");
  __CPROVER_assert(seen == 3, "lambda with by-value class parameter reads member");
  __CPROVER_assert(e.v == 0, "WRONG must FAIL");
  return 0;
}

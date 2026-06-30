// N5008 [class.base.init]/3 + [dcl.init.list]: a mem-initializer may initialize
// a base or member with a parenthesized expression-list, and an element of that
// list may itself be a braced-init-list.  So
//   holder(int a, int b, int t) : m({a, b}, t) {}
// is well-formed: the member m (of type mem) is initialized by mem({a,b}, t),
// where {a,b} initializes the first parameter (a pairlike) and t the second.
// g++ and clang++ accept it.
//
// This was a KNOWN BUG and is now fixed.  CBMC's C++ parser reported a parse
// error when, in a mem-initializer argument list, the FIRST argument was a
// braced-init-list followed by further arguments ( `m({a, b}, t)` ):
// rMemberInit's `( {` special case parsed only a single braced-init-list and
// then required `)`.  A braced-init-list as the sole argument ( `m({a, b})` )
// or as a non-first argument ( `m(t, {a, b})` ), and the same `f({a, b}, t)`
// call in an ordinary statement, all parsed correctly.  Fixed by parsing the
// full argument list via rFunctionArguments (each argument via rInitializeExpr,
// which accepts a leading `{`).  This unblocked refined_string_exprt's
// `: struct_exprt({_length, _content}, type)` (src/util/string_expr.h), which
// had failed goto-cc on simplify_expr.cpp.
//
// Non-vacuous: assertion 2 ("WRONG") must FAIL.  Flip to CORE once the parser
// accepts a leading braced-init-list argument in a mem-initializer.

extern "C" void __CPROVER_assert(int, const char *);

struct pairlike
{
  int a, b;
  pairlike(int x, int y) : a(x), b(y)
  {
  }
};

struct mem
{
  pairlike p;
  int t;
  mem(pairlike pp, int tt) : p(pp), t(tt)
  {
  }
};

struct holder
{
  mem m;
  holder(int a, int b, int t) : m({a, b}, t)
  {
  }
};

int main()
{
  holder h(1, 2, 3);
  __CPROVER_assert(
    h.m.p.a == 1 && h.m.p.b == 2 && h.m.t == 3,
    "braced-init-list as first mem-initializer argument");
  __CPROVER_assert(
    !(h.m.p.a == 1 && h.m.p.b == 2 && h.m.t == 3), "WRONG must FAIL");
  return 0;
}

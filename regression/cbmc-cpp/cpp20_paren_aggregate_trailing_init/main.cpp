// N5008 [dcl.init.aggr]/5 with [dcl.init.general]/16.6.2.2 (C++20
// parenthesized aggregate initialization, P0960): elements of the
// aggregate without a corresponding element in the expression-list are
// initialized from their default member initializer or
// copy-initialized from an empty initializer list -- NOT left
// indeterminate.
//
// This used to fail: both parenthesized-aggregate lowering paths in
// cpp_constructor assigned only the given operands, so `aggt x(1, 2)`
// with a third member read garbage from `x.c`.
//
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct aggt
{
  int a;
  int b;
  int c;
};

struct baset
{
  int v;
  template <typename U>
  baset(U u) : v(u)
  {
  }
};

struct derivedt : baset
{
  int w;
};

int main()
{
  aggt x(1, 2);
  __CPROVER_assert(x.a == 1 && x.b == 2, "given elements");
  __CPROVER_assert(x.c == 0, "trailing element value-initialized");

  derivedt d(7); // base from 7, w value-initialized
  __CPROVER_assert(d.v == 7, "base element");
  __CPROVER_assert(d.w == 0, "trailing member after base");
  return 0;
}

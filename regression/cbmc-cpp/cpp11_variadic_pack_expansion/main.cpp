// N5008 [temp.variadic]/5,7: when a pack expansion has zero arguments the
// expansion is discarded; with N arguments it expands to N.  A variadic
// constructor `X(A a, Rest... rest)` must drop the pack parameter when Rest is
// empty and expand it to one parameter per element otherwise, and a pack
// expansion in a function-call expression (`sum_of(rest...)`) must expand
// likewise.
//
// This exercises two pack-expansion contexts:
//   (1) the empty pack in the function-call-expression initializer
//       `sum(sum_of(rest...))` collapses to `sum(sum_of())`;
//   (2) a non-empty pack of two or more elements (`X<int,int,int>`) expands to
//       one parameter/argument per element, and the inner call-argument pack
//       in the function-call-expression initializer expands at its own level
//       (`sum(sum_of(rest$0, rest$1))`), so the recursive member function
//       template `sum_of` resolves.
//
// Non-vacuous: operands are nondet so the passing assertions are not folded,
// and the last assertion is a deliberately wrong claim that must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <class A, class... Rest>
struct X
{
  A value;
  int sum;
  X(A a, Rest... rest) : value(a), sum(sum_of(rest...))
  {
  }

private:
  static int sum_of()
  {
    return 0;
  }
  template <class T, class... Ts>
  static int sum_of(T t, Ts... ts)
  {
    return t + sum_of(ts...);
  }
};

int main()
{
  int v = nondet_int();
  int r1 = nondet_int();
  int r2 = nondet_int();

  // Empty pack: Rest = <>
  X<int> a(v);
  __CPROVER_assert(a.value == v, "empty pack value stored");
  __CPROVER_assert(a.sum == 0, "empty pack sum_of base case");

  // Non-empty pack: Rest = <int, int>
  X<int, int, int> b(v, r1, r2);
  __CPROVER_assert(b.value == v, "non-empty pack value stored");
  __CPROVER_assert(b.sum == r1 + r2, "non-empty pack sum_of");

  __CPROVER_assert(a.value == v + 1, "WRONG must FAIL");
  return 0;
}

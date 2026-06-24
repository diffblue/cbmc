// N5008 [temp.deduct.guide] / [over.match.class.deduct]: an explicit deduction
// guide's return type fixes the deduced specialization.  `P(T) -> P<T, int>`
// deduces T from the single argument and supplies `int` as the second template
// argument, so `P p{n}` is `P<int, int>`.
//
// Regression: CBMC ignored the guide's return type and tried to map the single
// argument onto both template parameters, failing with
// "not enough template arguments (expected 2, but got 1)".
template <typename A, typename B>
struct P
{
  A a;
  B b;
};
template <typename T>
P(T) -> P<T, int>;
int main()
{
  int n;        // nondet
  P p{n};       // guide: P<int,int>; aggregate a=n, b value-initialised to 0
  __CPROVER_assert(p.a == n, "guide P<int,int>: first member from argument");
  __CPROVER_assert(p.b == 0, "guide P<int,int>: second member value-initialised");
  return 0;
}

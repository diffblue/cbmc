// N5008 [over.match.class.deduct] + [temp.variadic]: a variadic class template
// deduces leading parameters positionally and the trailing parameter pack from
// the remaining arguments, so `T3{p, q, 99}` is `T3<int, int, int>`
// (Rest = <int>).
//
// Regression: CBMC's deduction collapsed equal argument types, deducing a
// single template argument and mis-binding the leading parameters.  The nondet
// operands p and q make the checks non-vacuous.
template <typename A, typename B, typename... Rest>
struct T3
{
  A x;
  B y;
  T3(A a, B b, Rest...) : x(a), y(b) {}
};
template <typename A, typename B, typename... Rest>
T3(A, B, Rest...) -> T3<A, B, Rest...>;
int main()
{
  int p, q; // nondet
  auto t = T3{p, q, 99}; // T3<int,int,int>, Rest = <int>
  __CPROVER_assert(t.x == p, "leading parameter A bound to first argument");
  __CPROVER_assert(t.y == q, "leading parameter B bound to second argument");
  return 0;
}

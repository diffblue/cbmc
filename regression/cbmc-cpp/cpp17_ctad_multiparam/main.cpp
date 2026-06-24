// N5008 [over.match.class.deduct]: each template parameter of a multi-parameter
// class template is deduced from the corresponding constructor argument,
// independently of whether two arguments share a type.
//
// Regression: CBMC's deduction collapsed equal argument types, so `Pair{1, 2}`
// produced a single deduced argument and failed with
// "not enough template arguments (expected 2, but got 1)".
template <typename A, typename B>
struct Pair
{
  A a;
  B b;
  Pair(A x, B y) : a(x), b(y) {}
};
template <typename A, typename B>
Pair(A, B) -> Pair<A, B>;
int main()
{
  Pair p{1, 2}; // both int: Pair<int,int>
  __CPROVER_assert(p.a == 1, "first component");
  __CPROVER_assert(p.b == 2, "second component");
  auto q = Pair{7, 'c'}; // Pair<int,char>
  __CPROVER_assert(q.a == 7, "auto-form first component");
  __CPROVER_assert(q.b == 'c', "auto-form second component (char)");
  return 0;
}

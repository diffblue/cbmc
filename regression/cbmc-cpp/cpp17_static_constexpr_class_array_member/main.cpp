// User-reported Issue 12.  N5008 [dcl.init.aggr]/4: an array of class type
// is initialised element by element from its braced list.  The braced list
// of an in-class `static constexpr V vs[N] = {V(..), V(..)}' was handed to
// the constructor machinery as ONE operand and became an N-argument
// constructor call ("found no match for symbol 'V'").  [class.static.data]
// /3: an `inline' static data member's in-class declaration is its
// definition (it was left extern, so its initialiser never ran).
extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int x;
  int y;
  constexpr V(int a, int b) : x(a), y(b)
  {
  }
};
struct P
{
  int x;
  int y;
};
struct A
{
  static constexpr V vs[2] = {V(1, 2), V(3, 4)};
  static constexpr V one[1] = {V(5, 6)};
  static constexpr P ps[2] = {{1, 2}, {3, 4}};
  static inline const V iv[2] = {V(7, 8), V(9, 10)};
  static inline const int ik = 11;
  static constexpr V vs3[3] = {V(1, 1), V(2, 2), V(3, 3)};
};
int main()
{
  __CPROVER_assert(
    A::vs[1].x == 3 && A::vs[0].y == 2, "N = 2, class-typed elements");
  __CPROVER_assert(A::one[0].y == 6, "N = 1");
  __CPROVER_assert(A::ps[1].y == 4, "brace elements of an aggregate");
  __CPROVER_assert(A::iv[1].x == 9 && A::iv[0].y == 8, "inline const array");
  __CPROVER_assert(A::ik == 11, "inline const scalar");
  __CPROVER_assert(
    A::vs3[2].x == 3 && sizeof(A::vs3) == 3 * sizeof(V), "N = 3");
  return 0;
}

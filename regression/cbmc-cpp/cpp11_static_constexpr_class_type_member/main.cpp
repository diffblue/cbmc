// N5008 [class.static.data]/3, [dcl.constexpr]/1: a constexpr static data
// member is implicitly inline; its in-class declaration is its definition.
// Class-type members were kept as extern "macros" whose substitution folds
// scalar reads only, so `A::p.x' read nondet; a constructor-initialised one
// crashed the solver once it became an object (typeless `this').
#include <array>
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int x;
  int y;
  int get() const
  {
    return x + y;
  }
};
constexpr P make_p(int a)
{
  return P{a, a + 1};
}
struct Q
{
  int v;
  constexpr Q(int v) : v(v)
  {
  }
};
struct W
{
  int e[3];
};
struct A
{
  static constexpr P p = {.x = 3, .y = 4};
  static constexpr P q = {5, 6};
  static constexpr P r = make_p(3);
  static constexpr P pa[2] = {make_p(1), make_p(5)};
  static constexpr std::array<int, 3> arr = {1, 2, 3};
  static constexpr std::array<int, 3> arr2 = {{4, 5, 6}};
  static constexpr W w = {1, 2, 3};
  static constexpr W w2 = {{7, 8, 9}};
  static constexpr Q c1{11};
  static constexpr Q c2 = Q(12);
  static constexpr Q c3 = 13;
};
template <class T>
struct B
{
  static constexpr P p = make_p(sizeof(T));
  static constexpr std::array<T, 2> arr = {T(4), T(5)};
};
int main()
{
  __CPROVER_assert(A::p.x == 3 && A::p.get() == 7, "member designators");
  __CPROVER_assert(A::q.y == 6, "positional aggregate");
  __CPROVER_assert(A::r.x == 3 && A::r.y == 4, "constexpr call initialiser");
  __CPROVER_assert(A::pa[1].y == 6, "array of aggregates");
  __CPROVER_assert(
    A::arr[1] == 2 && A::arr.size() == 3, "std::array, brace elision");
  __CPROVER_assert(A::arr2[2] == 6, "std::array, full braces");
  __CPROVER_assert(A::w.e[1] == 2 && A::w2.e[2] == 9, "nested array member");
  __CPROVER_assert(
    A::c1.v == 11 && A::c2.v == 12 && A::c3.v == 13, "constructor-initialised");
  __CPROVER_assert(
    B<char>::p.y == 2 && B<int>::p.x == 4, "template, class-type member");
  __CPROVER_assert(B<short>::arr[1] == 5, "template, std::array member");
  const P *addr = &A::p;
  __CPROVER_assert(addr->x == 3, "address of a class-type constexpr member");
  return 0;
}

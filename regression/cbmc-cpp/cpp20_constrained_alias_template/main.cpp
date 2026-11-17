// N5008 [temp.names]/9: naming a constrained alias template with arguments
// that do not satisfy its constraints is a substitution failure.  libstdc++
// 13 (C++20) constrains the overloads of make_shared by
// `template<class T> requires (extent_v<T> != 0) using _BoundedArray = T;'
// in their return types; the constraint was ignored and make_shared<T>()
// chose the bounded-array overload for every T.
#include <memory>
#include <mutex>
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
constexpr unsigned long extent_v = 0;
template <class T, unsigned long N>
constexpr unsigned long extent_v<T[N]> = N;
template <class T>
  requires(extent_v<T> != 0)
using Bounded = T;
template <class T>
  requires(extent_v<T> == 0)
using NonArray = T;
template <class T>
struct box
{
  int kind;
  box(int k) : kind(k)
  {
  }
};
template <class T, class... A>
box<NonArray<T>> make(A &&...)
{
  return box<T>(1);
}
template <class T>
box<Bounded<T>> make()
{
  return box<T>(2);
}
struct M
{
  int m;
};
int main()
{
  __CPROVER_assert(make<M>().kind == 1, "not an array");
  __CPROVER_assert(make<M[3]>().kind == 2, "bounded array");
  auto p = std::make_shared<std::mutex>();
  __CPROVER_assert(p.use_count() == 1, "make_shared");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// N5008 [over.match.class.deduct]: the guides of class template argument
// deduction, as std::vector's: a deduction guide with a defaulted
// parameter ([over.match.viable]/2.3) and defaulted template parameters,
// one of which fails substitution for a non-iterator ([temp.deduct.general]
// /5, /8); for a braced list, the guide from an initializer-list
// constructor first ([over.match.list]/1), whose parameter names the
// class's typedef of T; a class template in an inline namespace, named
// qualified ([namespace.qual]/2); and a template-id naming the class
// template although it has a guide ([temp.deduct.guide]/1).
#include <initializer_list>
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct alloc
{
};
template <class It>
struct traits
{
  using value_type = typename It::value_type;
};
template <bool B, class T = void>
struct enable
{
};
template <class T>
struct enable<true, T>
{
  using type = T;
};
template <class It>
using require_iterator = typename enable<It::is_iterator>::type;
namespace lib
{
inline namespace v1
{
template <class T, class A = alloc<T>>
struct vec
{
  typedef T value_type;
  typedef A allocator_type;
  int n;
  vec(std::initializer_list<value_type> l, const A & = A()) : n(l.size())
  {
  }
  template <class It>
  vec(It, It, const A & = A()) : n(7)
  {
  }
};
template <
  class It,
  class V = typename traits<It>::value_type,
  class A = alloc<V>,
  class = require_iterator<It>>
vec(It, It, A = A()) -> vec<V, A>;
} // namespace v1
} // namespace lib
struct iter
{
  using value_type = int;
  static constexpr bool is_iterator = true;
};
template <class X, class Y>
struct same
{
  static const bool value = false;
};
template <class X>
struct same<X, X>
{
  static const bool value = true;
};
int main()
{
  lib::vec a(iter{}, iter{});
  static_assert(same<decltype(a), lib::vec<int>>::value, "from the guide");
  lib::vec b{1, 2, 3};
  static_assert(same<decltype(b), lib::vec<int>>::value, "from the list");
  __CPROVER_assert(
    a.n == 7 && b.n == 3 && sizeof(lib::vec<int>) == sizeof(int), "deduced");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// N5008 [meta.unary.prop] + [temp.variadic]/5: is_constructible<T> (an empty
// argument pack) is default-constructibility.  libstdc++ writes every
// is_default_constructible<T> and the SFINAE default template argument of
// std::stack's default constructor as is_constructible<T, Args...> with an
// EMPTY Args pack, e.g. bool_constant<__is_constructible(T, Args...)>.
//
// Regression: CBMC left the empty pack as the (now empty) pack NAME, which
// type-checked to the empty type instead of nil, so __is_constructible(T, <>)
// took the "construct T from void" path and wrongly reported false -- breaking
// std::stack (and thus util/expr_iterator.h's visit_pre_template traversal used
// by exprt::visit, a silent soundness loss).  It also over-approximated the
// no-argument case to true; here the empty-pack query is evaluated ACCURATELY:
// a class with a user-declared constructor but no default constructor is not
// default-constructible.  g++/clang++ agree.  assertion.4 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

template <int __v>
struct integral_constant
{
  static constexpr int value = __v;
};
template <bool __v>
using bool_constant = integral_constant<__v>;
template <typename T, typename... A>
using is_ctible = bool_constant<__is_constructible(T, A...)>;

struct D
{
  int v;
  D() : v(7) {}
}; // user default ctor
struct Agg
{
  int v;
}; // aggregate: implicit default ctor
struct ND
{
  int v;
  ND(int x) : v(x) {}
}; // no default ctor

int main()
{
  __CPROVER_assert(
    is_ctible<int>::value == 1, "is_constructible<int> (empty pack) is true");
  __CPROVER_assert(
    is_ctible<D>::value == 1, "is_constructible<D> (user default ctor) is true");
  __CPROVER_assert(
    is_ctible<ND>::value == 0,
    "is_constructible<ND> (no default ctor) is false");
  __CPROVER_assert(is_ctible<int>::value == 0, "WRONG must FAIL");
  return 0;
}

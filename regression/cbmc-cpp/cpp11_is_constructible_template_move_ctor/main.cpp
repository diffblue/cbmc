// N5008 [meta.unary.prop]: is_constructible<T, Args...> is true iff the variable
// definition `T t(declval<Args>()...);` is well-formed.  Here T = pair<const
// int, int> has a template move converting constructor `pair(pair<U1,U2>&&)`,
// and the argument `declval<pair<int,int>&&>()` is an rvalue of pair<int,int>,
// which binds to that constructor's `pair<U1,U2>&&` parameter (U1=U2=int).  So
// __is_constructible(pair<const int,int>, pair<int,int>&&) is TRUE (confirmed
// with g++ and clang++).
//
// KNOWN BUG: CBMC's __is_constructible builtin reports FALSE for this case.  It
// only fails when BOTH the converting constructor parameter is an rvalue
// reference AND the argument is an rvalue reference -- a const-lvalue-reference
// converting constructor, or a by-value argument, are handled correctly.  CBMC
// evaluates __is_constructible via implicit_conversion_sequence with a source
// expression built from the rvalue-reference type, which does not bind to the
// rvalue-reference constructor parameter.
//
// This is the root of std::map/std::unordered_map insert failing for a
// convertible pair (the constrained `insert(_Pair&&)` overload's
// is_constructible<value_type, _Pair&&> guard) -- src/util/expr.cpp,
// expr_util.cpp, irep_serialization.cpp.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Reduced from
// preprocessed <utility>/<type_traits> via cvise.  Flip to CORE once
// __is_constructible binds an rvalue argument to an rvalue-reference converting
// constructor.

extern "C" void __CPROVER_assert(int, const char *);

template <class, class>
struct pair
{
  template <class U1, class U2> pair(pair<U1, U2> &&); // template move converting ctor
};

int main()
{
  __CPROVER_assert(
    __is_constructible(pair<const int, int>, pair<int, int> &&),
    "is_constructible via template move converting ctor");
  __CPROVER_assert(
    !__is_constructible(pair<const int, int>, pair<int, int> &&),
    "WRONG must FAIL");
  return 0;
}

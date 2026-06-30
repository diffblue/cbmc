// N5008 [meta.unary.prop]: is_constructible<T, Args...> is true iff
// `T t(declval<Args>()...);` is well-formed.  std::pair<const int,int> has a
// converting constructor template `pair(pair<U1,U2>&&)` and pair<int,int>&& is
// convertible to pair<const int,int>, so the trait is TRUE (g++ and clang++
// agree).
//
// This was a KNOWN BUG (CBMC reported FALSE) and is now fixed.  Root cause
// (N5008 [meta.rel]/2): libstdc++'s C++17 converting move constructor
//   template<class _U1, class _U2, typename __enable_if_t<
//     _PCCFP<_U1,_U2>::template _MoveConstructiblePair<_U1,_U2>() && ...,
//     bool> = true> pair(pair<_U1,_U2>&&);
// is constrained via
//   _PCCFP<_U1,_U2> = conditional<!is_same<_T1,_U1> || !is_same<_T2,_U2>,
//                                 _PCC<true,_T1,_T2>, _PCC<false,_T1,_T2>>::type
// For pair<const int,int> from pair<int,int>, !is_same<const int,int> is true,
// so _PCCFP selects _PCC<true,...> whose _MoveConstructiblePair() is true ->
// the constructor is viable.  CBMC's __is_same ignored cv-qualifiers
// (irept::operator== treats #constant/#volatile as comments), so
// is_same<const int,int> was wrongly TRUE, _PCCFP selected _PCC<false,...>,
// _MoveConstructiblePair() was false, the enable_if was ill-formed, and the
// constructor was dropped ("found no match for symbol 'pair'") -> trait false.
// Fixed by making __is_same compare cv-qualifiers (see
// regression/cbmc-cpp/cpp11_is_same_cv_qualifiers).
//
// This was the root of std::map / std::unordered_map insert failing for a
// convertible pair (the constrained `insert(_Pair&&)` overload's
// is_constructible<value_type,_Pair&&> guard).
//
// Non-vacuous (assertion 2 must FAIL).

#include <utility>
#include <type_traits>

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  __CPROVER_assert(
    std::is_constructible<std::pair<const int, int>, std::pair<int, int> &&>::value,
    "pair<const int,int> is_constructible from pair<int,int>&&");
  __CPROVER_assert(
    !std::is_constructible<std::pair<const int, int>, std::pair<int, int> &&>::value,
    "WRONG must FAIL");
  return 0;
}

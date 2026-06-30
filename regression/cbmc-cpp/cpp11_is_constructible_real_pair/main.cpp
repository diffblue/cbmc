// N5008 [meta.unary.prop]: is_constructible<T, Args...> is true iff
// `T t(declval<Args>()...);` is well-formed.  std::pair<const int,int> has a
// converting constructor template `pair(pair<U1,U2>&&)` and pair<int,int>&& is
// convertible to pair<const int,int>, so the trait is TRUE (g++ and clang++
// agree).
//
// KNOWN BUG: CBMC reports it FALSE.  Root cause (verified by tracing the
// front-end), N5008 [temp.deduct.call]/4 + [temp.deduct.type]:
//
//   * __is_constructible delegates to the user-defined-conversion / temporary-
//     construction path, which (correctly, per [over.match.copy]) tries to
//     construct pair<const int,int> from pair<int,int>&&.
//   * libstdc++'s C++17 converting move constructor is
//       template<class _U1, class _U2,
//                typename __enable_if_t<
//                  _PCCFP<_U1,_U2>::template _MoveConstructiblePair<_U1,_U2>()
//                  && _PCCFP<_U1,_U2>::template
//                       _ImplicitlyMoveConvertiblePair<_U1,_U2>(),
//                  bool> = true>
//       pair(pair<_U1,_U2>&&);
//   * Deducing the constructor's template parameters from the argument
//     pair<int,int>&& deduces _U1=int but leaves _U2 UNASSIGNED.  (A minimal
//     hand-written pair with the same converting ctor shape deduces both, so
//     the loss of _U2 is specific to the real declaration's surrounding
//     machinery; this is why the bug only reproduces with the header.)
//   * Because _U2 is unassigned, template_map::apply cannot substitute it into
//     the __enable_if_t<...> non-type parameter's condition, so typecheck_type
//     of the parameter type throws and the constructor candidate is dropped
//     (guess_function_template_args returns nil).  No converting constructor is
//     found -> "found no match for symbol 'pair'" -> __is_constructible false.
//
// user_defined_conversion_sequence is NOT the culprit: it correctly delegates
// the template converting constructor to new_temporary; the defect is in the
// constructor-template argument deduction it relies on.
//
// This is the root of std::map / std::unordered_map insert failing for a
// convertible pair (the constrained `insert(_Pair&&)` overload's
// is_constructible<value_type,_Pair&&> guard) -- src/util/expr.cpp,
// expr_util.cpp, pointer_predicates.cpp, irep_serialization.cpp.
//
// Non-vacuous (assertion 2 must FAIL).  Flip to CORE once constructor-template
// argument deduction deduces every template parameter of the converting
// constructor for this source.

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

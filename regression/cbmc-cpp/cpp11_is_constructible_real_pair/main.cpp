// N5008 [meta.unary.prop]: is_constructible<T, Args...> is true iff
// `T t(declval<Args>()...);` is well-formed.  std::pair<const int,int> has a
// converting constructor template `pair(pair<U1,U2>&&)` and pair<int,int>&& is
// convertible to pair<const int,int>, so the trait is TRUE (g++ and clang++
// agree).
//
// KNOWN BUG: CBMC reports it FALSE.  Root cause (verified by tracing the
// front-end), N5008 [temp.deduct.call] + [temp.arg]:
//
//   * __is_constructible delegates (correctly, [over.match.copy]) to
//     constructing pair<const int,int> from pair<int,int>&&.
//   * libstdc++'s C++17 converting move constructor (stl_pair.h:708) is
//       template<class _U1, class _U2, typename __enable_if_t<
//         _PCCFP<_U1,_U2>::template _MoveConstructiblePair<_U1,_U2>()
//         && _PCCFP<_U1,_U2>::template _ImplicitlyMoveConvertiblePair<_U1,_U2>(),
//         bool> = true>
//       pair(pair<_U1,_U2>&&);
//   * Constructor-template argument deduction CORRECTLY binds _U1=int, _U2=int
//     (the template_map holds `...::651::_U1 -> int` and `...::651::_U2 -> int`).
//   * BUT template_mapt::apply fails to substitute those bound _U1/_U2
//     references where they are nested inside the `ambiguous` condition
//     expression of the __enable_if_t<...> non-type parameter type.  They
//     survive as bare cpp_names, so typecheck_type of the parameter type throws
//     and the candidate is dropped ("found no match for symbol 'pair'") -> the
//     trait is false.
//   * A hand-written pair whose enable_if is spelled `enable_if<...>::type`
//     reproduces neither (apply substitutes there); the gap is specific to the
//     __enable_if_t alias wrapping a member-function-template constraint
//     expression, hence the header dependency.
//
// user_defined_conversion_sequence is NOT the culprit: it correctly delegates
// the template converting constructor to new_temporary.  The defect is the
// substitution gap in template_mapt::apply.
//
// This is the root of std::map / std::unordered_map insert failing for a
// convertible pair (the constrained `insert(_Pair&&)` overload's
// is_constructible<value_type,_Pair&&> guard) -- src/util/expr.cpp,
// expr_util.cpp, pointer_predicates.cpp, irep_serialization.cpp.
//
// Non-vacuous (assertion 2 must FAIL).  Flip to CORE once template_mapt::apply
// substitutes deduced parameters inside an enable_if non-type-parameter's
// condition expression.

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

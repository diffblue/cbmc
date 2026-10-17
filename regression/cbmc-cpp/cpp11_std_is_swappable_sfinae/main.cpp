// Minimal reproducer for an open CBMC bug: processing libstdc++'s
// `std::is_swappable<T>` (and transitively, `std::array<T, N>`)
// emits spurious type-checker errors during SFINAE substitution.
//
// Root site: /usr/include/c++/13/type_traits line 2721:
//   template<typename _Tp>
//     _Require<__not_<__is_tuple_like<_Tp>>,
//              is_move_constructible<_Tp>,
//              is_move_assignable<_Tp>>
//     swap(_Tp&, _Tp&) noexcept(...);
//
// Substituting `_Tp = double` into the return type
//   _Require<__not_<__is_tuple_like<double>>, ...>
// (which unfolds to
//   __enable_if_t<__and_<__not_<__is_tuple_like<double>>, ...>::value>
// via the alias at type_traits line 2224, with `__not_<_Pp>` defined as
//   : __bool_constant<!bool(_Pp::value)>
// at type_traits line 181) requires CBMC's type checker to evaluate
// `_Pp::value` where `_Pp` is a class-template specialisation.
//
// CBMC's current implementation instead reaches the
// `typecheck_expr_main` fallback in src/ansi-c/c_typecheck_expr.cpp
// with an `ID_struct_tag` expression whose identifier is
//   `std::tag-__not_<std::tag-__is_tuple_like<double>>`
// and emits:
//   error: unexpected expression: struct_tag
//     * #source_location: ...
//     * identifier: ...
// (an `irep::pretty()` dump, not a clean diagnostic) and then:
//   error: found no match for symbol 'swap', candidates are: ...
//
// Per [temp.deduct]/8 ("any other invalid type or expression ... is
// a deduction failure"), a substitution failure inside the return
// type of a function-template candidate must be absorbed silently
// during overload resolution — no user-visible error should be
// emitted, and the candidate is simply removed.
//
// `std::is_swappable<double>::value` must be well-formed and
// evaluate to true (double is trivially swappable).

#include <type_traits>

int main()
{
  static_assert(std::is_swappable<double>::value, "double is swappable");
  return 0;
}

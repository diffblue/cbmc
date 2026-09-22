// A variadic class template recursing on its own pack, one element shorter
// per level (libstdc++ 11's __and_ / __or_ conjunction): and_<6 traits>
// instantiates and_<5>, which instantiates and_<4>, ...  The recursion
// converges on the argument count; the elaboration depth limit for
// re-entrant instantiations of one template (two levels) silently skipped
// the third level, so and_ of five or more traits never got a `value'
// (every libstdc++ 11 tuple<A, B, C> constructor constraint evaluated
// false: std::bind with three placeholders, forward_as_tuple of three).
template <bool v>
struct bool_constant
{
  static constexpr bool value = v;
};
template <class...>
struct and_ : bool_constant<true>
{
};
template <class B1>
struct and_<B1> : B1
{
};
template <class B1, class B2, class... Bn>
struct and_<B1, B2, Bn...> : bool_constant<B1::value && and_<B2, Bn...>::value>
{
};
typedef bool_constant<true> T;
typedef bool_constant<false> F;

int main()
{
  static_assert(and_<T, T, T, T>::value, "four");
  static_assert(and_<T, T, T, T, T>::value, "five");
  static_assert(and_<T, T, T, T, T, T, T, T, T>::value, "nine");
  static_assert(!and_<T, T, T, T, F>::value, "five, last false");
  static_assert(!and_<T, T, T, T, T, T, F, T>::value, "eight, one false");
  __CPROVER_assert(and_<T, T, T, T, T, T>::value, "six at run time");
  return 0;
}

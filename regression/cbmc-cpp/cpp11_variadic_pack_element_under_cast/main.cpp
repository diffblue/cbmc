// N5008 [temp.variadic]/5: the i-th element of a pack expansion
// instantiates the pattern with the i-th element of each pack it names.
// A pack reference under a cast (`!bool(Bn::value)', libstdc++'s __or_fn
// and __and_fn) was substituted for the first element only, so
// `__or_<false_type, true_type>' was false_type and every trait built on
// it -- `__is_unsigned_integer', hence SFINAE on std::from_chars for
// unsigned -- was wrong.  Header-free model of <type_traits>' __or_.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool v>
struct bool_constant
{
  static constexpr bool value = v;
};
using true_type = bool_constant<true>;
using false_type = bool_constant<false>;
template <bool, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template <bool C, typename T = void>
using enable_if_t = typename enable_if<C, T>::type;
template <typename T, typename...>
using first_t = T;

template <typename... Bn>
auto or_fn(int) -> first_t<false_type, enable_if_t<!bool(Bn::value)>...>;
template <typename... Bn>
auto or_fn(...) -> true_type;
template <typename... Bn>
struct or_ : decltype(or_fn<Bn...>(0))
{
};

template <typename... Bn>
auto and_fn(int) -> first_t<true_type, enable_if_t<bool(Bn::value)>...>;
template <typename... Bn>
auto and_fn(...) -> false_type;
template <typename... Bn>
struct and_ : decltype(and_fn<Bn...>(0))
{
};

// the C-style and static_cast spellings
template <typename... Bn>
auto g(int) -> first_t<int, enable_if_t<!(bool)Bn::value>...>;
template <typename... Bn>
auto g(...) -> char;
template <typename... Bn>
auto h(int) -> first_t<int, enable_if_t<!static_cast<bool>(Bn::value)>...>;
template <typename... Bn>
auto h(...) -> char;

int main()
{
  __CPROVER_assert(or_<false_type, true_type>::value, "or second true");
  __CPROVER_assert(or_<true_type, false_type>::value, "or first true");
  __CPROVER_assert(!or_<false_type, false_type>::value, "or none");
  __CPROVER_assert(or_<false_type, false_type, true_type>::value, "or third");
  __CPROVER_assert(!or_<>::value, "or empty");
  __CPROVER_assert(!and_<true_type, false_type>::value, "and second false");
  __CPROVER_assert(and_<true_type, true_type>::value, "and both");
  __CPROVER_assert(and_<>::value, "and empty");
  __CPROVER_assert(sizeof(g<false_type, true_type>(0)) == 1, "c-style cast");
  __CPROVER_assert(sizeof(h<false_type, true_type>(0)) == 1, "static_cast");
  __CPROVER_assert(
    sizeof(h<false_type, false_type>(0)) == sizeof(int), "static_cast none");
  return 0;
}

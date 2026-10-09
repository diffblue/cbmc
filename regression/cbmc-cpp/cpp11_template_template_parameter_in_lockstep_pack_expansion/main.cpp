// N5008 [temp.variadic]/5,7: `Tr<L, R>::value...' expands the packs L and
// R in lockstep; Tr is a template template parameter bound to `same'.
// libc++'s __tuple_sfinae_base::__do_test is written this way, and
// __tuple_impl's converting constructor is constrained on it.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool...>
struct bools
{
};

template <class...>
struct types
{
};

template <class T, class U>
struct same
{
  static constexpr bool value = __is_same(T, U);
};

template <template <class, class> class Tr, class... L, class... R>
auto two(types<L...>, types<R...>) -> bools<Tr<L, R>::value...>;

int main()
{
  __CPROVER_assert(
    __is_same(
      decltype(two<same>(types<int, char>{}, types<int, long>{})),
      bools<true, false>),
    "lockstep");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

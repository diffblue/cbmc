extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct tup
{
};
template <class T, class U>
struct same
{
  static constexpr bool value = false;
};
template <class T>
struct same<T, T>
{
  static constexpr bool value = true;
};
template <class... B>
constexpr bool all_v = (B::value && ...);
// N5008 [temp.spec.partial.general]/1 (variable templates),
// [temp.variadic]/5: Dests and Srcs are deduced from the arguments and
// expanded in lockstep
template <bool Same, class Dest, class... Srcs>
constexpr bool constructible_v0 = false;
template <class... Dests, class... Srcs>
constexpr bool constructible_v0<true, tup<Dests...>, Srcs...> =
  all_v<same<Dests, Srcs>...>;
template <class Dest, class... Srcs>
constexpr bool constructible_v = constructible_v0<true, Dest, Srcs...>;
int main()
{
  __CPROVER_assert(constructible_v<tup<int, char>, int, char>, "matching");
  __CPROVER_assert(!constructible_v<tup<int, char>, char, int>, "mismatching");
  __CPROVER_assert(constructible_v<tup<int>, char>, "WRONG (must FAIL)");
  return 0;
}

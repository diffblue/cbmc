// N5008 [temp.spec.partial.order]/1, [temp.deduct.type]/9: for tup<double>
// both partial specializations below match, the second with R deduced to an
// empty pack ([temp.arg.explicit]/4).  The second is more specialized: its
// pattern tup<F, R...> deduces the first's tup<Ts...>, but not the other way
// round (9.2: the pack expansion Ts... cannot be matched by the non-pack F).
// The shape of libstdc++ 11's __tuple_count, behind variant's converting
// constructor (std::variant<int, double> v = 2.5).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, T v>
struct ic
{
  static constexpr T value = v;
};
template <class A, class B>
struct same : ic<bool, false>
{
};
template <class A>
struct same<A, A> : ic<bool, true>
{
};
template <class...>
struct tup
{
};
template <class T, class Tu>
struct cnt;
template <class T, class... Ts>
struct cnt<T, tup<Ts...>> : ic<unsigned, 0>
{
};
template <class T, class F, class... R>
struct cnt<T, tup<F, R...>>
  : ic<unsigned, cnt<T, tup<R...>>::value + same<T, F>::value>
{
};
template <class Tu>
struct first
{
  static constexpr int value = 0;
};
template <class F, class... R>
struct first<tup<F, R...>>
{
  static constexpr int value = 1;
};
template <class... Ts>
struct first<tup<Ts...>>
{
  static constexpr int value = 2;
};
int main()
{
  __CPROVER_assert(
    cnt<double, tup<>>::value == 0 && cnt<double, tup<double>>::value == 1 &&
      cnt<double, tup<int, double>>::value == 1 &&
      cnt<int, tup<int, int, double>>::value == 2,
    "counts");
  __CPROVER_assert(
    first<tup<double>>::value == 1 && first<tup<int, char>>::value == 1 &&
      first<tup<>>::value == 2 && first<int>::value == 0,
    "more specialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

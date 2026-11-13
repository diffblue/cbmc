// N5008 [temp.inst]/16: only the total depth of recursive instantiations is
// bounded.  A partial specialization that peels a type list while keeping
// another argument, `F<L<H, T...>, Len>' instantiating `F<L<T...>, Len>',
// converges.  Xcode 26's libc++ computes std::aligned_storage's default
// alignment so (__find_max_align over a list of ten types), which
// std::function's small-buffer member uses.
extern "C" void __CPROVER_assert(bool, const char *);

template <class... Ts>
struct L
{
};
template <int N>
struct A
{
  static const int value = N;
};
template <class TL, int Len>
struct F;
template <class H, int Len>
struct F<L<H>, Len>
{
  static const int value = H::value;
};
template <class H, class... T, int Len>
struct F<L<H, T...>, Len>
{
  static const int value =
    H::value > F<L<T...>, Len>::value ? H::value : F<L<T...>, Len>::value;
};
template <class H, class... T>
struct G;
template <class H>
struct G<H>
{
  static const int value = 1;
};
template <class H, class... T>
struct G
{
  static const int value = 1 + G<T...>::value;
};

int main()
{
  static_assert(F<L<A<1>, A<2>, A<3>, A<4>, A<5>>, 0>::value == 5, "five");
  static_assert(
    F<L<A<3>, A<9>, A<2>, A<7>, A<1>, A<8>, A<4>, A<6>, A<5>, A<0>>,
      24>::value == 9,
    "ten");
  static_assert(G<int, int, int, int, int, int>::value == 6, "pack only");
  int n = F<L<A<1>, A<2>, A<3>, A<4>, A<5>, A<6>>, 0>::value;
  __CPROVER_assert(n == 6, "six at run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

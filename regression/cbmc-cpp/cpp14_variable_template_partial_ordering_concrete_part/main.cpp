extern "C" void __CPROVER_assert(bool, const char *);
template <class T = void>
struct equal_to
{
};
template <class A, class P>
constexpr int pick = 0;
// N5008 [temp.spec.partial.order]/1, [temp.deduct.type]/1: deducing
// `pick<A, C *>' from `pick<A, int *>' succeeds (C = int), the reverse does
// not (int * is not C *), so `pick<A, int *>' is more specialized; likewise
// `equal_to<>' over `equal_to<C>' (the MSVC STL's
// _Can_memcmp_elements_with_pred, behind std::equal)
template <class A, class C>
constexpr int pick<A, C *> = 1;
template <class A>
constexpr int pick<A, int *> = 2;
template <class A, class C>
constexpr int pick<A, equal_to<C>> = 3;
template <class A>
constexpr int pick<A, equal_to<>> = 4;
int main()
{
  __CPROVER_assert(
    pick<char, int *> == 2 && pick<char, long *> == 1 &&
      pick<char, equal_to<>> == 4 && pick<char, equal_to<int>> == 3,
    "more specialized chosen");
  __CPROVER_assert(pick<char, int *> == 1, "WRONG (must FAIL)");
  return 0;
}

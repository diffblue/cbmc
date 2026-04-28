// std::sort in C++20 mode.
// GCC 16 std::less<void> uses nested requires that CBMC can't parse.
// ARM has template resolution issues with swap in sort.
#if defined(__GNUC__) && __GNUC__ >= 13 && __GNUC__ <= 15 && \
    !defined(__aarch64__) && !defined(__arm__)
#  include <algorithm>
int main()
{
  int a[] = {3, 1, 4};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1, "sorted");
}
#elif !defined(__GNUC__) && !defined(_MSC_VER)
#  include <algorithm>
int main()
{
  int a[] = {3, 1, 4};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1, "sorted");
}
#else
int main()
{
}
#endif

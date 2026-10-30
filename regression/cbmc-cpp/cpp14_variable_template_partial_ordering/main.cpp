// N5008 [temp.spec.partial.order]/1 for variable templates
// ([temp.spec.partial.general]/1): of several matching partial
// specializations the more specialised one is selected.
extern "C" void __CPROVER_assert(bool, const char *);

template <typename T, unsigned I = 0>
inline constexpr unsigned long ext = 0;
template <typename T, unsigned long N>
inline constexpr unsigned long ext<T[N], 0> = N;
template <typename T, unsigned long N, unsigned I>
inline constexpr unsigned long ext<T[N], I> = ext<T, I - 1>;
template <typename T, unsigned I>
inline constexpr unsigned long ext<T[], I> = ext<T, I - 1>;

template <typename T>
inline constexpr int kind = 0;
template <typename T>
inline constexpr int kind<T *> = 1;
template <typename T>
inline constexpr int kind<const T *> = 2;

int main()
{
  static_assert(ext<int[5]> == 5, "rank 0 of int[5]");
  static_assert(ext<int[5][7], 1> == 7, "rank 1");
  static_assert(ext<int[5][7]> == 5, "rank 0 of 2-d");
  static_assert(ext<int> == 0, "non-array: primary");
  static_assert(ext<int[][3], 1> == 3, "unknown bound, rank 1");
  static_assert(kind<int *> == 1, "T*");
  static_assert(kind<const int *> == 2, "const T* is more specialised");
  __CPROVER_assert(ext<char[9]> == 9, "runtime use");
  __CPROVER_assert(ext<char[9]> == 0, "WRONG (must FAIL)");
  return 0;
}

// N5008 [temp.variadic]/8, [temp.deduct.general]/5: in
// `enable_if<all_int<U...>::value, int>::type = 0' the expansion U...
// names every deduced element of U.  With one deduced element the pack was
// bound as a scalar only and U... expanded to no argument, so the constraint
// tested all_int<> (true) and the candidate was never removed.  This is the
// shape of libc++'s tuple(_Up &&...) constraint.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <class... U>
struct all_int
{
  static constexpr bool value = (__is_same(int, U) && ...);
};

template <class... U, typename enable_if<all_int<U...>::value, int>::type = 0>
int f(U &&...)
{
  return 1;
}
int f(...)
{
  return 2;
}

template <class... T>
struct tup
{
  template <class... U>
  struct enable_u
  {
    static constexpr bool value =
      sizeof...(U) == sizeof...(T) && (__is_constructible(T, U) && ...);
  };
  template <
    class... U,
    typename enable_if<enable_u<U...>::value, int>::type = 0>
  tup(U &&...)
  {
  }
  tup() = default;
};

int main()
{
  char *p = nullptr;
  __CPROVER_assert(f(p) == 2, "one element removes the candidate");
  __CPROVER_assert(f(1) == 1, "one element keeps the candidate");
  __CPROVER_assert(f(1, p) == 2, "two elements remove the candidate");
  static_assert(
    !__is_convertible(const tup<int, tup<int>> &, tup<int>),
    "converting constructor removed");
  static_assert(__is_constructible(tup<int>, int), "constructor kept");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.type]/1: an expression of type "reference to T" is adjusted
// to T before further analysis, so `static_cast<A &&>(l) == ...' compares
// the referred objects (the MSVC STL's equal_to<void>, used by std::equal)
template <class T = void>
struct eq
{
  constexpr bool operator()(const T &l, const T &r) const
  {
    return l == r;
  }
};
template <>
struct eq<void>
{
  template <class A, class B>
  [[nodiscard]] constexpr auto operator()(A &&l, B &&r) const
    noexcept(noexcept(static_cast<A &&>(l) == static_cast<B &&>(r)))
      -> decltype(static_cast<A &&>(l) == static_cast<B &&>(r))
  {
    return static_cast<A &&>(l) == static_cast<B &&>(r);
  }
};
int main()
{
  int a = 3, b = 3;
  __CPROVER_assert(static_cast<int &>(a) == static_cast<int &>(b), "cast ==");
  __CPROVER_assert(
    static_cast<int &&>(a) < static_cast<int &>(b) + 1, "cast <");
  __CPROVER_assert(eq<>{}(3, 3), "literals");
  __CPROVER_assert(eq<>{}(a, b), "lvalues");
  __CPROVER_assert(!eq<>{}(a, 4), "unequal");
  __CPROVER_assert(eq<>{}(a, 4), "WRONG (must FAIL)");
}

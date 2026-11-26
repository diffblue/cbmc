extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&declval() noexcept;
struct true_type
{
  static const bool value = true;
};
struct false_type
{
  static const bool value = false;
};
namespace stdx
{
template <typename T>
void swap(T &a, T &b)
{
  T tmp = a;
  a = b;
  b = tmp;
}
struct do_is_swappable
{
  template <
    typename T,
    typename = decltype(swap(declval<T &>(), declval<T &>()))>
  static true_type test(int);
  template <typename>
  static false_type test(...);
};
template <typename T>
struct is_swappable : decltype(do_is_swappable::test<T>(0))
{
};
} // namespace stdx
struct NoCopy
{
  NoCopy() = default;
  NoCopy(const NoCopy &) = delete;
  NoCopy &operator=(const NoCopy &) = delete;
};
struct Plain
{
  int v;
};
int main()
{
  // the unevaluated operand names swap<NoCopy>; its declaration is
  // instantiated, its definition (which would be ill-formed) is not
  __CPROVER_assert(
    stdx::is_swappable<NoCopy>::value,
    "trait is true: the expression is valid");
  __CPROVER_assert(
    stdx::is_swappable<Plain>::value, "trait for a copyable type");
  Plain a{1}, b{2};
  stdx::swap(a, b);
  __CPROVER_assert(a.v == 2 && b.v == 1, "swap really called");
  __CPROVER_assert(a.v == 1, "WRONG (must FAIL)");
}

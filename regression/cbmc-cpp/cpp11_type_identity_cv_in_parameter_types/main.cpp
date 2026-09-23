extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
struct S
{
  int f(int) const;
  int g(int);
};
template <class T, class U>
struct same_t
{
  static constexpr bool value = false;
};
template <class T>
struct same_t<T, T>
{
  static constexpr bool value = true;
};
int main()
{
  __CPROVER_assert(
    !std::is_same<void (*)(const int *), void (*)(int *)>::value,
    "cv inside a parameter pointee distinguishes function pointer types");
  __CPROVER_assert(
    !std::is_same<const int *, int *>::value, "cv inside a pointee");
  __CPROVER_assert(
    !std::is_same<int (S::*)(int) const, int (S::*)(int)>::value,
    "cv-qualified pmf distinct");
  __CPROVER_assert(
    !std::is_same<decltype(&S::f), decltype(&S::g)>::value,
    "decltype(&S::f) const vs non-const");
  __CPROVER_assert(
    std::is_same<int (S::*)(int) const, decltype(&S::f)>::value,
    "equal cv-qualified pmf types are the same");
  // the typedef spelling of a cv-qualified pointer-to-member function type
  // keeps the cv-qualifier-seq too (it was dropped: only the alias
  // spelling and the type-id form reached the function type)
  typedef int (S::*TPMF)(int) const;
  __CPROVER_assert(
    std::is_same<TPMF, int (S::*)(int) const>::value &&
      !std::is_same<TPMF, int (S::*)(int)>::value,
    "typedef of a const pmf");
  // the partial-specialization form of the comparison ([temp.class.spec.match])
  __CPROVER_assert(
    !same_t<void (*)(const int *), void (*)(int *)>::value &&
      same_t<void (*)(const int *), void (*)(const int *)>::value,
    "is_same<T, T> partial specialization sees the parameter cv");
  return 0;
}

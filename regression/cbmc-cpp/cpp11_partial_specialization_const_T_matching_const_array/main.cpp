extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct I
{
  static const int value = 0;
};
// [basic.type.qualifier]/3: `const char[3]' is "const T" with T = char[3],
// so I<const char[3]> derives from I<char[3]>, which is the primary template.
// libstdc++'s incrementable_traits<const _Tp> : incrementable_traits<_Tp>
// takes this path for a string literal.
template <class T>
struct I<const T> : I<T>
{
  static const int depth = I<T>::value + 1;
  typedef T type;
};
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
int main()
{
  __CPROVER_assert(I<const char[3]>::depth == 1, "const array");
  __CPROVER_assert(
    same<I<const char[3]>::type, char[3]>::value, "T is the unqualified array");
  __CPROVER_assert(
    same<I<const int[2][2]>::type, int[2][2]>::value,
    "array of arrays of const int");
  __CPROVER_assert(I<char[3]>::value == 0, "non-const array: primary");
  __CPROVER_assert(I<const char[3]>::depth != 1, "WRONG (must FAIL)");
}

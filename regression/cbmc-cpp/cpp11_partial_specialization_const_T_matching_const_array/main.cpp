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
};
int main()
{
  __CPROVER_assert(I<const char[3]>::depth == 1, "const array");
  __CPROVER_assert(I<const char[3]>::depth != 1, "WRONG (must FAIL)");
}

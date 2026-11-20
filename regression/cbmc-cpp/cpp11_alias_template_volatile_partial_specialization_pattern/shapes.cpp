extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class...>
using ident = T;
template <class T>
using ident1 = T;
// [dcl.type.cv]/1, [temp.alias]/2: an alias of a cv-qualified type keeps
// its qualifiers
template <class T>
struct V
{
  static const int v = 0;
};
template <class T>
struct V<volatile T>
{
  static const int v = 1;
};
// [temp.deduct.partial]: `const volatile T' is more specialized than
// `const T' and `volatile T'
template <class T>
struct B
{
  static const int v = 0;
};
template <class T>
struct B<const T>
{
  static const int v = 1;
};
template <class T>
struct B<volatile T>
{
  static const int v = 2;
};
template <class T>
struct B<const volatile T>
{
  static const int v = 3;
};
template <class T>
struct C
{
  static const int v = 0;
};
template <class T>
struct C<ident<const T, int>>
{
  static const int v = 1;
};
template <class T>
struct C<ident<const volatile T, int>>
{
  static const int v = 3;
};
struct tup
{
};
int main()
{
  __CPROVER_assert(
    V<ident<volatile tup, int>>::v == 1 && V<ident1<volatile tup>>::v == 1 &&
      V<ident<volatile int, int>>::v == 1 &&
      V<ident<const volatile tup, int>>::v == 1,
    "volatile through an alias");
  __CPROVER_assert(
    B<const volatile tup>::v == 3 && B<const volatile int>::v == 3 &&
      B<const int>::v == 1 && B<volatile int>::v == 2,
    "more qualified is more specialized");
  __CPROVER_assert(
    C<const volatile tup>::v == 3 && C<const tup>::v == 1,
    "through an alias as well");
  __CPROVER_assert(C<const volatile tup>::v == 1, "WRONG (must FAIL)");
}

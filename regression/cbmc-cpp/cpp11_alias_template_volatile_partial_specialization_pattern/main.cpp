extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class...>
using ident = T;
// [temp.alias]/2: A<ident<volatile T, int>> is A<volatile T>
template <class T>
struct A
{
  static const int v = 0;
};
template <class T>
struct A<ident<const T, int>>
{
  static const int v = 1;
};
template <class T>
struct A<ident<volatile T, int>>
{
  static const int v = 2;
};
template <class T>
struct A<ident<const volatile T, int>>
{
  static const int v = 3;
};
struct tup
{
};
int main()
{
  __CPROVER_assert(
    A<tup>::v == 0 && A<const tup>::v == 1, "unqualified, const");
  __CPROVER_assert(A<volatile tup>::v == 2, "volatile through the alias");
  __CPROVER_assert(
    A<const volatile tup>::v == 3, "const volatile through the alias");
  __CPROVER_assert(A<volatile tup>::v == 0, "WRONG (must FAIL)");
}

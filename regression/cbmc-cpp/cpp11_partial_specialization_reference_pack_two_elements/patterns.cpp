extern "C" void __CPROVER_assert(bool, const char *);
// [temp.deduct.type]/9, [temp.spec.partial.match]: a trailing pack expansion
// whose pattern is not a bare pack is compared with each remaining argument
template <class... T>
struct L
{
};
template <class T1, class... Z>
struct S
{
  static const int v = 0;
};
template <class T1, class... Z>
struct S<T1, const Z &...>
{
  static const int v = 2;
};
template <class T1, class T2>
struct S<T1, const T2 &>
{
  static const int v = 3;
};
template <class... Z>
struct P
{
  static const int v = 0;
};
template <class... Z>
struct P<Z *...>
{
  static const int v = 1;
};
template <class... Z>
struct Q
{
  static const int v = 0;
};
template <class... Z>
struct Q<L<Z>...>
{
  static const int v = 1;
};
template <class A, class... Z>
struct R
{
  static const int v = 0;
};
template <class A, class... Z>
struct R<A, A (*)(Z)...>
{
  static const int v = 1;
};
int main()
{
  __CPROVER_assert(
    S<int, const int &, const char &>::v == 2, "differing elements");
  __CPROVER_assert(
    S<int, const int &, int &>::v == 0, "one element does not match");
  __CPROVER_assert(S<int, const int &>::v == 3, "one element");
  __CPROVER_assert(
    P<int *, char *, long *>::v == 1 && P<int *, char>::v == 0, "Z *...");
  __CPROVER_assert(
    Q<L<int>, L<char>>::v == 1 && Q<L<int>, int>::v == 0, "L<Z>...");
  __CPROVER_assert(
    R<int, int (*)(char), int (*)(long)>::v == 1, "pattern naming A");
  __CPROVER_assert(
    R<int, int (*)(char), long (*)(long)>::v == 0, "A must agree");
  __CPROVER_assert(P<int *, char *, long *>::v != 1, "WRONG (must FAIL)");
}

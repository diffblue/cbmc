extern "C" void __CPROVER_assert(bool, const char *);
// [temp.deduct.type]/9.2, [temp.spec.partial.order]: during partial
// ordering, an argument that is a pack expansion does not deduce a
// parameter that is not, so the specialization without the pack is more
// specialized (N5008 [temp.deduct.type] Example 4)
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
template <class... T>
struct R
{
  static const int v = 0;
};
template <class... T>
struct R<int, T...>
{
  static const int v = 1;
};
template <class T>
struct R<int, T>
{
  static const int v = 2;
};
int main()
{
  __CPROVER_assert(S<int, const int &>::v == 3, "Example 4: #3");
  __CPROVER_assert(R<int, char>::v == 2, "non-pack is more specialized");
  __CPROVER_assert(R<int, char, char>::v == 1, "only the pack matches");
  __CPROVER_assert(R<int, char>::v != 2, "WRONG (must FAIL)");
}

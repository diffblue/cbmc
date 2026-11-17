extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.deduct.type] Example 4: S<int, const int &, const int &>
// matches only #2, `S<T1, const Z &...>' with Z = {int, int}
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
int main()
{
  __CPROVER_assert(S<int, const int &, const int &>::v == 2, "#2");
  __CPROVER_assert(
    S<int, const int &, const int &>::v != 2, "WRONG (must FAIL)");
}

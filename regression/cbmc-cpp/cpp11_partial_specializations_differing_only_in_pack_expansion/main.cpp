// N5008 [temp.variadic]/5, [temp.spec.partial.general]: `S<T, const U &...>'
// and `S<T, const U &>' are different partial specializations.  Their
// internal identifiers ignored the pack expansion (and whether a parameter
// is a pack), so when both used the parameter name U the later one replaced
// the earlier one, and S<int, const int &, const int &> used the primary.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class... U>
struct S
{
  static const int v = 1;
};
template <class T, class... U>
struct S<T, const U &...>
{
  static const int v = 2;
};
template <class T, class U>
struct S<T, const U &>
{
  static const int v = 3;
};

template <class... T>
struct X
{
  static const int v = 1;
};
template <class... T>
struct X<T *...>
{
  static const int v = 2;
};
template <class T>
struct X<T *>
{
  static const int v = 3;
};

int main()
{
  __CPROVER_assert(S<int, const int &, const int &>::v == 2, "pack");
  __CPROVER_assert(S<int, const int &>::v == 3, "single");
  __CPROVER_assert(S<int, int>::v == 1, "primary");
  __CPROVER_assert(X<int *, char *>::v == 2, "pointer pack");
  __CPROVER_assert(X<int *>::v == 3, "pointer");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

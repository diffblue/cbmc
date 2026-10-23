extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct tup
{
};
template <class>
struct only;
// N5008 [temp.variadic]/5: `A &&...' expands to one element per pack
// element, `A *...' and `const A...' likewise; [temp.deduct]/5 substitutes
// the deduced arguments into the return type before the candidate is used
template <>
struct only<tup<int &&, int &&>>
{
  typedef int type;
};
template <>
struct only<tup<int *, int *>>
{
  typedef long type;
};
template <>
struct only<tup<const int, const int>>
{
  typedef short type;
};
struct binder
{
  template <class... A>
  typename only<tup<A &&...>>::type rref(A...)
  {
    return sizeof...(A);
  }
  template <class... A>
  typename only<tup<A *...>>::type ptr(A...)
  {
    return 10 * sizeof...(A);
  }
};
template <class... A>
typename only<tup<const A...>>::type cst(A...)
{
  return 100 * sizeof...(A);
}
int main()
{
  binder b;
  __CPROVER_assert(b.rref(1, 2) == 2, "A &&...");
  __CPROVER_assert(b.ptr(1, 2) == 20, "A *...");
  __CPROVER_assert(cst(1, 2) == 200, "const A...");
  __CPROVER_assert(cst(1, 2) == 2, "WRONG (must FAIL)");
  return 0;
}

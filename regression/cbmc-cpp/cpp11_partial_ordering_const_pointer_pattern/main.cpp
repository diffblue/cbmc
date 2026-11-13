// N5008 [temp.func.order]/3, [temp.deduct.partial]/5-7: partial ordering
// removes only the top-level reference and cv-qualifiers of the compared
// parameter types; beneath them the types must be identical
// ([temp.deduct.type]/1).  So f(const T *) is more specialized than f(T *)
// (deducing `const T *' from `U *' fails), and f(&ci) selects it.  Both
// were at least as specialized as each other and f(T *) was chosen with
// T = const int.  Also: T deduced from a `const T' pattern has the
// qualifier removed ([temp.deduct.type]/8), so g(const T &, T) deduces
// T = int from (const int, int).  [temp.deduct.partial]/9: of two
// reference patterns identical after the transformations, h(const T &)
// is more specialized than h(T &) (/9.2) and m(T &) than m(T &&) (/9.1).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
int f(T *)
{
  return 1;
}
template <class T>
int f(const T *)
{
  return 2;
}
template <class T>
int g(const T &, T)
{
  return sizeof(T);
}
template <class T>
int h(T &, T &)
{
  return 1;
}
template <class T>
int h(const T &, const T &)
{
  return 2;
}
template <class T>
int m(T &&)
{
  return 1;
}
template <class T>
int m(T &)
{
  return 2;
}
int main()
{
  int i = 0;
  const int ci = 0;
  char c = 0;
  __CPROVER_assert(f(&i) == 1, "non-const pointer");
  __CPROVER_assert(f(&ci) == 2, "const pointer picks const T *");
  __CPROVER_assert(g(ci, i) == sizeof(int), "const T deduces T without const");
  __CPROVER_assert(h(i, i) == 1 && h(ci, ci) == 2, "reference patterns");
  __CPROVER_assert(f(&c) == 1, "char pointer");
  __CPROVER_assert(m(i) == 2 && m(1) == 1, "lvalue reference over forwarding");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

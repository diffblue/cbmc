// N5008 [expr.sub]/1, [over.sub]/1, [temp.variadic]/5: the expression-list
// of a subscript may contain pack expansions, also after other elements and
// with an empty pack (operator[] then takes no arguments).
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  int operator[]() const
  {
    return 7;
  }
  int operator[](int i) const
  {
    return i;
  }
  int operator[](int i, int j, int k) const
  {
    return i * 100 + j * 10 + k;
  }
};
template <class... A>
int all(const M &m, A... a)
{
  return m[a...];
}
template <class... A>
int lead(const M &m, A... a)
{
  return m[1, a...];
}
template <class... A>
int twice(const M &m, A... a)
{
  return m[a * 2 ...];
}
int main()
{
  M m;
  __CPROVER_assert(
    all(m) == 7 && all(m, 4) == 4 && all(m, 1, 2, 3) == 123 &&
      lead(m, 2, 3) == 123 && twice(m, 1, 2, 3) == 246,
    "subscript pack expansions");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

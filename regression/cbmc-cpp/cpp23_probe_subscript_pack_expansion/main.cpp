// N5008 [over.sub], [expr.sub], [temp.variadic]: pack expansion in a
// subscript.
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  int operator[](int i, int j) const
  {
    return i * 10 + j;
  }
};
template <class... A>
int g(A... a)
{
  M m;
  return m[a...];
}
int main()
{
  __CPROVER_assert(g(1, 2) == 12, "pack expansion in a subscript");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

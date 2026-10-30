extern "C" void __CPROVER_assert(bool, const char *);
struct choice_t
{
  int strategy;
};
struct cpo
{
  template <class T>
  static constexpr choice_t choice = {2};
  // N5008 [stmt.if]/2, [dcl.spec.auto.general]/10: the first return
  // statement is in a discarded statement and takes no part in the
  // deduction, so the return type is int (the shape of the MSVC STL's
  // ranges::iter_move, whose _Choice<_Ty>._Strategy selects the branch)
  template <class T>
  decltype(auto) h(T) const
  {
    if constexpr(choice<T>.strategy == 1)
      return 1.0;
    else
      return 20;
  }
};
int main()
{
  cpo c;
  __CPROVER_assert(__is_same(decltype(c.h(0)), int), "deduced as int");
  __CPROVER_assert(__is_same(decltype(c.h(0)), double), "WRONG (must FAIL)");
  return 0;
}

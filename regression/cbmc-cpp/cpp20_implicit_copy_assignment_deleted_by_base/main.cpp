extern "C" void __CPROVER_assert(bool, const char *);
class pbase
{
  friend struct pr;
  pbase() = default;
  pbase(const pbase &) = default;
  pbase &operator=(const pbase &) = delete;
};
struct nonesuch
{
};
struct pr : private pbase
{
  const int first;
  int second;
  pr(int a, int b) : first(a), second(b)
  {
  }
  pr(const pr &) = default;
  // not a copy assignment operator: the implicit one is declared, and
  // defined as deleted ([class.copy.assign]/7: the base's is deleted)
  pr &operator=(const nonesuch &)
  {
    return *this;
  }
};
template <class L, class R>
concept assignable = requires(L l, R &&r)
{
  l = static_cast<R &&>(r);
};
int main()
{
  // N5008 [expr.prim.req.general]/5: the requirement is not satisfied
  static_assert(!assignable<pr &, const pr &>);
  pr p(1, 2);
  pr q = p;
  __CPROVER_assert(q.first == 1 && q.second == 2, "copy constructed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

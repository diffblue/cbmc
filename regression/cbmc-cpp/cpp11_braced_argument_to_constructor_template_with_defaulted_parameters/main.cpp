extern "C" void __CPROVER_assert(bool, const char *);
struct L
{
  int n;
};
template <class A, class B>
struct P
{
  A first;
  B second;
  // like libstdc++'s pair(const _T1 &, const _T2 &): a template whose
  // parameters are never deduced from the call, only defaulted
  template <class U1 = A, class U2 = B>
  P(const A &a, const B &b) : first(a), second(b)
  {
  }
  // like pair(_U1 &&, _U2 &&): deduction from a braced-init-list fails
  // ([temp.deduct.call]/1: non-deduced context), so it is not viable
  template <class U1, class U2>
  P(U1 &&a, U2 &&b) : first(a), second(b)
  {
  }
};
int main()
{
  P<int, P<unsigned, L>> a(1, {2u, L{3}});
  __CPROVER_assert(a.second.second.n == 3, "nested braced argument");
  __CPROVER_assert(a.second.second.n == 4, "WRONG (must FAIL)");
}

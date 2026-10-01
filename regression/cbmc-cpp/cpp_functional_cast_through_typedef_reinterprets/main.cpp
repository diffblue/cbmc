extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long U;
typedef long *P;
typedef int *Q;
int main()
{
  int i = 0;
  const void *a = &i;
  // [expr.type.conv]/1.1: T(e) is the cast expression (T)e, which may be a
  // reinterpret_cast or const_cast ([expr.cast]/4); libstdc++'s
  // __waiter_pool_base::_S_for computes `uintptr_t(__addr)'
  U k = U(a);
  __CPROVER_assert(k == (U)a, "pointer to integer");
  P p = P(&i);
  __CPROVER_assert((void *)p == &i, "pointer to unrelated pointer");
  const int *c = &i;
  Q q = Q(c);
  __CPROVER_assert(q == &i, "cast away const");
  __CPROVER_assert(k != (U)a, "WRONG (must FAIL)");
}

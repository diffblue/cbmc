extern "C" void __CPROVER_assert(bool, const char *);
struct F
{
};
struct E
{
  int v;
  explicit E(int q) : v(q)
  {
  }
  E(long) : v(2)
  {
  }
  E(F) : v(5)
  {
  }
};
int main()
{
  // [over.match.copy]/1.1: only the converting constructors are candidates
  // for copy-initialization -- E(long) for 1, E(F) for f; direct
  // initialization ([over.match.ctor]) considers E(int) too
  E a = 1;
  F f;
  E b = f;
  E c(1);
  E d = c;
  __CPROVER_assert(a.v == 2, "converting constructor");
  __CPROVER_assert(b.v == 5, "class argument");
  __CPROVER_assert(c.v == 1 && d.v == 1, "direct and copy");
  __CPROVER_assert(a.v != 2, "WRONG (must FAIL)");
}

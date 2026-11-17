enum kind_t : int
{
  K0,
  K1 = 5
};
struct rec
{
  int a;
  kind_t k;
  int b;
};
struct outer
{
  rec r;
  int c;
};
extern rec g_r;
int get_b();
int sum(outer o);
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  outer o{{1, K1, 2}, 3};
  g_r.b = 4;
  __CPROVER_assert(sum(o) == 11 && get_b() == 4, "values");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

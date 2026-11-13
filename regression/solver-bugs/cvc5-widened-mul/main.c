int main(void)
{
  unsigned int a;
  int x;
  __CPROVER_assume(a > 0 && a < 10);
  __CPROVER_assume(x > 0);
  int xp1 = (int)((unsigned)x + 1u);
  long long p1 = (long long)a * (long long)xp1;
  long long p2 = (long long)a * (long long)x;
  __CPROVER_assert(!(p1 < p2), "p1 >= p2");
  return 0;
}

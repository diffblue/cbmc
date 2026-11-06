long long nondet_ll(void);

int main(void)
{
  long long v = nondet_ll();
  __CPROVER_assume(v > 4096 && v < 8192);
  char *p = (char *)v;
  __CPROVER_assert(p != 0, "holds: v in [4097,8191] cannot be null");
  return 0;
}

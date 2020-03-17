int f(void)
{
  return 1;
}

int g(void)
{
  return 2;
}

int h(void)
{
  return 3;
}

typedef int (*fp_t)(void);

fp_t fp;

void main()
{
  int cond;
  fp = cond ? f : g;
  int res = fp();
  __CPROVER_assert(res == 1, "");
  __CPROVER_assert(res == 2, "");
  __CPROVER_assert(res == 1 || res == 2, "");
}

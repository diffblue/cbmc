int check(int cond)
{
  return cond;
}

int main()
{
  int x;
  int *p = &x;
  if(check(!__CPROVER_r_ok(p, sizeof(int))))
  {
    __CPROVER_assert(0, "must be unreachable");
  }
}

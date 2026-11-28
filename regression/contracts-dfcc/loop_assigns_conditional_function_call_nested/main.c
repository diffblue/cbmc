int cond(int *a)
{
  int r;
  // taking the address makes r a local that the instrumentation tracks
  int *p = &r;
  *p = a != 0;
  return r;
}

int valid(int *a)
{
  return cond(a);
}

void foo(int *a)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_assigns(i; valid(a): a[0])
    __CPROVER_loop_invariant(0 <= i && i <= 3)
    // clang-format on
    {
      a[0] = i;
    }
}

int main()
{
  int a[3];
  foo(a);
  // makes cond, but not valid, reachable, so that only cond is instrumented
  __CPROVER_assert(cond(a), "cond");
  return 0;
}

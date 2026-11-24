int cond(int *a)
{
  return a != 0;
}

void foo(int *a)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_assigns(i; cond(a): a[0])
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
  return 0;
}

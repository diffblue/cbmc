int a, b, c, d, e, f;

void g(void)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_assigns(i, a, b, c, d, e, f)
    __CPROVER_loop_invariant(0 <= i && i <= 3)
    // clang-format on
    {
      a = i;
      b = i;
      c = i;
      d = i;
      e = i;
      f = i;
    }
}

int main()
{
  for(int j = 0; j < 2; j++)
    // clang-format off
    __CPROVER_assigns(j, a, b, c, d, e, f)
    __CPROVER_loop_invariant(0 <= j && j <= 2)
    // clang-format on
    {
      g();
    }
  return 0;
}

int x;

void set_x(int *p, int v)
{
  *p = v;
}

void second(char *s)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 3)
    // clang-format on
    {
      if(x == 0)
        first(s);
    }
}

void first(char *s)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 3)
    // clang-format on
    {
      set_x(&x, 1);
    }
}

int main(void)
{
  char s[2] = {'1', 0};
  second(s);
  __CPROVER_assert(x == 0 || x == 1, "x is 0 or 1");
  return 0;
}

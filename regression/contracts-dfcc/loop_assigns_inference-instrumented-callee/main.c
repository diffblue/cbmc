int x;

void a_mid(void);

void l_loop(void)
{
  for(int i = 0; i < 3; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 3)
    // clang-format on
    {
      if(x == 0)
        a_mid();
    }
}

void c_set(int *p, int v)
{
  *p = v;
}

void a_mid(void)
{
  c_set(&x, 1);
}

int main(void)
{
  l_loop();
  __CPROVER_assert(x == 0 || x == 1, "x is 0 or 1");
  return 0;
}

int main()
{
  int x = 0;
  int *y = &x;

  while(*y <= 0 && *y < 10)
    // clang-format off
    __CPROVER_loop_invariant(1 == 1)
    __CPROVER_decreases(10 - x)
    // clang-format on
    {
      x++;
    }
}

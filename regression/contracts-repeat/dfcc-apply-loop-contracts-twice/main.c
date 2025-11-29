int main(void)
{
  int i = 0;
  int s = 0;
  // clang-format off
  while(i < 10)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    __CPROVER_decreases(10 - i)
  {
    s += i;
    ++i;
  }
  // clang-format on
  return s;
}

int main()
{
  int i = 0;
  int N = 10;
  while(i != N)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N)
    __CPROVER_decreases(N - i) 
    __CPROVER_decreases(42)
    // clang-format on
    {
      i++;
    }

  return 0;
}

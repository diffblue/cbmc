
int main()
{
  int i = 0;
  int N = 10;
  while(i != N)
    // clang-format off
    __CPROVER_loop_invariant(i <= N)
    __CPROVER_decreases(N - i)
    // clang-format on
    {
      i++;
    }

  return 0;
}

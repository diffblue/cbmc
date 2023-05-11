int main()
{
  int i = 0;
  int j = 0;
  int N = 10;
  while(i < N)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N && 0 <= j && j <= N)
    __CPROVER_decreases(N - i, j)
    // clang-format on
    {
      if(j < N)
      {
        j++;
      }
      else
      {
        i++;
        j = 0;
      }
    }
}

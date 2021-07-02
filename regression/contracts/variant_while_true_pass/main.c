
int main()
{
  int i = 0;
  int N = 10;
  while(1 == 1)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N)
    __CPROVER_decreases(N - i)
    // clang-format on
    {
      if(i == 10)
      {
        break;
      }
      i++;
    }

  return 0;
}

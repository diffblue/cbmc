
int main()
{
  int i = 0;
  int N = 10;
  while(i != N)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N) 
    __CPROVER_decreases(i)
    // clang-format on
    {
      i++;
    }

  return 0;
}

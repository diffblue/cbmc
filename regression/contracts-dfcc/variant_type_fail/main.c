int main()
{
  int a[10];
  int *p = a;
  int i = 0;
  int N = 10;
  while(i != N)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N && p == a + i)
    __CPROVER_decreases(N - i, p)
    // clang-format on
    {
      i++;
      p++;
    }

  return 0;
}

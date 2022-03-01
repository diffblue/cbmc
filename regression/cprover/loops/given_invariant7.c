#define N 100

int main()
{
  int array[N];

  for(int i = 0; i != N; i++)
    // clang-format off
    __CPROVER_loop_invariant(i >= 0 && i <= N) // passes
  {
    array[i] = 0; // safe and passes
  }
  // clang-format on

  return 0;
}

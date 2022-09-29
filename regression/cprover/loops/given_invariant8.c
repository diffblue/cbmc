int main()
{
  int n;
  __CPROVER_assume(n >= 0);
  int array[n];

  for(int i = 0; i != n; i++)
    // clang-format off
    __CPROVER_loop_invariant(
      i >= 0 && i <= n && sizeof(array) == sizeof(int) * n) // passes
  {
    array[i] = 0; // safe and passes
  }
  // clang-format on

  return 0;
}

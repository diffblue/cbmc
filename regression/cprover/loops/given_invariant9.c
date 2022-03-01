void *malloc(__CPROVER_size_t);

int main()
{
  int n;
  __CPROVER_assume(n >= 0);
  int *array = malloc(sizeof(int) * n);

  for(int i = 0; i != n; i++)
    // clang-format off
    __CPROVER_loop_invariant(i >= 0 && i <= n)
    __CPROVER_loop_invariant(__CPROVER_r_ok(array, sizeof(int) * n))
  {
    array[i] = 0; // safe and passes
  }
  // clang-format on

  return 0;
}

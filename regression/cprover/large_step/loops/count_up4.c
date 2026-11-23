_Bool nondet_bool();

int main()
{
  unsigned int i, j, size;

  __CPROVER_assume(size % 2 == 0);
  __CPROVER_assume(size < (0u - 2));

  j = 0;
  for(i = 0; i < size; i += 2, j++)
    // clang-format off
    __CPROVER_loop_invariant(i >= 0 && i <= size && size < (0u-2) && size % 2 == 0 && i == j * 2)
  {
    __CPROVER_assert(j < size / 2, "property 1");
  }
  // clang-format on

  return 0;
}

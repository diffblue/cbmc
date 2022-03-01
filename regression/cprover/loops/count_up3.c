_Bool nondet_bool();

int main()
{
  unsigned int i, size;

  __CPROVER_assume(size % 2 == 0);
  __CPROVER_assume(size < (0u - 2));

  for(i = 0; i < size; i += 2)
    // clang-format off
    __CPROVER_loop_invariant(
      i >= 0 && i <= size && i % 2 == 0 && size < (0u - 2) && size % 2 == 0)
  {
  }
  // clang-format on

  __CPROVER_assert(i == size, "property 1"); // passes

  return 0;
}

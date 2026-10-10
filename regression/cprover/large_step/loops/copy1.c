int main()
{
  char *input, *output;
  __CPROVER_size_t size;

  __CPROVER_assume(__CPROVER_r_ok(input, size));
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(input) == 0);
  __CPROVER_assume(__CPROVER_w_ok(output, size));
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(output) == 0);

  for(__CPROVER_size_t i = 0; i < size; i++)
    // clang-format off
    __CPROVER_loop_invariant(i >= 0 && i <= size)
    __CPROVER_loop_invariant(__CPROVER_r_ok(input, size))
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(input) == 0)
    __CPROVER_loop_invariant(__CPROVER_w_ok(output, size))
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(output) == 0)
    // clang-format on
    {
      output[i] = input[i];
    }
}

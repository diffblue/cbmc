const char *HEX_CHARS = "0123456789abcdef";

int main()
{
  __CPROVER_size_t input_size;
  unsigned char *input;
  char *output;

  __CPROVER_assume(input_size < 100);
  __CPROVER_assume(__CPROVER_r_ok(input, input_size));
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(input) == 0);
  __CPROVER_assume(__CPROVER_w_ok(output, input_size * 2));
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(output) == 0);

  __CPROVER_assert(__CPROVER_r_ok(HEX_CHARS, 16), "property 1");
  __CPROVER_assert(__CPROVER_POINTER_OFFSET(HEX_CHARS) == 0, "property 2");

  __CPROVER_assume(!__CPROVER_same_object(&HEX_CHARS, output));

  __CPROVER_size_t written = 0;
  for(__CPROVER_size_t i = 0; i < input_size; ++i)
    // clang-format off
    __CPROVER_loop_invariant(input_size < 100)
    __CPROVER_loop_invariant(i >= 0 && i <= input_size)
    __CPROVER_loop_invariant(__CPROVER_r_ok(input, input_size))
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(input) == 0)
    __CPROVER_loop_invariant(__CPROVER_r_ok(HEX_CHARS, 16))
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(HEX_CHARS) == 0)
    __CPROVER_loop_invariant(written == i * 2)
    __CPROVER_loop_invariant(__CPROVER_w_ok(output, input_size * 2))
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(output) == 0)
    __CPROVER_loop_invariant(!__CPROVER_same_object(&HEX_CHARS, output))
    // clang-format on
    {
      unsigned char ch = input[i];
      char hex0 = HEX_CHARS[ch >> 4 & 0x0f];
      char hex1 = HEX_CHARS[ch & 0x0f];
      output[written++] = hex0;
      output[written++] = hex1;
    }

  return 0;
}

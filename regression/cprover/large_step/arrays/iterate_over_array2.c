#define size_t __CPROVER_size_t
#define false 0
#define true 1

_Bool find_zero(const void *const array, const size_t array_len)
{
  const unsigned char *array_bytes = array;

  // iterate over array
  for(size_t i = 0; i < array_len; ++i)
    // clang-format off
    __CPROVER_loop_invariant(i >= 0 && i <= array_len)
    __CPROVER_loop_invariant(__CPROVER_POINTER_OFFSET(array_bytes) == 0)
    __CPROVER_loop_invariant(__CPROVER_r_ok(array_bytes, array_len))
    // clang-format on
    {
      if(array_bytes[i] == 0)
      {
        return true;
      }
    }

  return false;
}

int main()
{
  unsigned char array[10];
  size_t array_len = 10;
  find_zero(array, array_len);
}

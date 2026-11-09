typedef __CPROVER_size_t size_t;

_Bool returns_a_range(const char *base, size_t size, size_t pos, size_t *length)
  // clang-format off
  __CPROVER_requires(__CPROVER_r_ok(base, size))
  __CPROVER_requires(pos <= size)
  __CPROVER_requires(__CPROVER_rw_ok(length))
  __CPROVER_assigns(*length)
  __CPROVER_ensures(__CPROVER_return_value ==> __CPROVER_old(pos) + *length <= size)
// clang-format on
{
  // skip any number of double quotes
  size_t start = pos;
  _Bool result = 0;

  while(pos < size && base[pos] == '"')
    // clang-format off
    __CPROVER_loop_invariant(__CPROVER_r_ok(base, size))
    __CPROVER_loop_invariant(__CPROVER_rw_ok(length))
    __CPROVER_loop_invariant(!result)
    // clang-format on
    {
      // out to be loop invariant
      __CPROVER_assert(__CPROVER_old(pos) == start, "property 1");
      pos++;
    }

  if(pos > start)
  {
    *length = pos - start;
    result = 1;
  }

  return result;
}

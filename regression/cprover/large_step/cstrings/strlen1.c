__CPROVER_size_t my_strlen(const char *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_cstring(p))
  __CPROVER_ensures(__CPROVER_return_value == __CPROVER_cstrlen(p))
// clang-format on
{
  __CPROVER_size_t result = 0;

  while(*p != 0)
    // clang-format off
    __CPROVER_loop_invariant(__CPROVER_is_cstring(p))
    __CPROVER_loop_invariant(p - __CPROVER_old(p) == result)
    __CPROVER_loop_invariant(result <= __CPROVER_cstrlen(__CPROVER_old(p)))
  {
    p++;
    result++;
  }
  // clang-format on

  return result;
}

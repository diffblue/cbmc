int main()
{
  const char *p;

  __CPROVER_assume(__CPROVER_is_cstring(p));

  while(*p != 0)
    // clang-format off
    __CPROVER_loop_invariant(__CPROVER_is_cstring(p))
  {
    p++;
  }
  // clang-format on

  return 0;
}

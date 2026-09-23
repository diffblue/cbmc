int main()
{
  const char *p;

  __CPROVER_assume(__CPROVER_is_cstring(p));

  // unrelated
  const char *q = 0;

  __CPROVER_assert(__CPROVER_is_cstring(p), "p is still a cstring");

  return 0;
}

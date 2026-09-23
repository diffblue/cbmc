int main()
{
  const char *p, *q;
  __CPROVER_assume(p == q);
  __CPROVER_assert(
    __CPROVER_is_cstring(p) == __CPROVER_is_cstring(q), "property 1"); // passes

  return 0;
}

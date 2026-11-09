int main()
{
  const char *p;

  __CPROVER_assume(__CPROVER_is_cstring(p));
  __CPROVER_assume(*p != 0);

  p++;

  __CPROVER_assert(__CPROVER_is_cstring(p), "property 1");
  __CPROVER_assert(__CPROVER_r_ok(p), "property 2");

  return 0;
}

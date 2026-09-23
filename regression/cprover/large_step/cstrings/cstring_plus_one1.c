int main()
{
  const char *p;
  __CPROVER_assume(__CPROVER_is_cstring(p));

  if(*p != 0)
    __CPROVER_assert(__CPROVER_is_cstring(p + 1), "property 1"); // passes

  return 0;
}

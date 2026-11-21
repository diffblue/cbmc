int main()
{
  const char *string;

  __CPROVER_assume(__CPROVER_is_cstring(string));

  const char *p = string;

  __CPROVER_assert(__CPROVER_is_cstring(p), "property 1"); // passes

  return 0;
}

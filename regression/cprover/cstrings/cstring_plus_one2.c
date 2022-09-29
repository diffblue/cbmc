int main()
{
  const char *p;
  __CPROVER_assume(__CPROVER_is_cstring(p));

  if(*p != 0)
  {
    p++; // might modify the string
    __CPROVER_assert(__CPROVER_is_cstring(p), "property 1"); // passes
  }

  return 0;
}

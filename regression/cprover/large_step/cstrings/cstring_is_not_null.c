int main()
{
  const char *p;
  __CPROVER_assume(__CPROVER_is_cstring(p));

  // p can't be null
  __CPROVER_assert(p != 0, "property");

  return 0;
}

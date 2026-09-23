int main()
{
  const char *p;
  __CPROVER_assume(__CPROVER_is_cstring(p));

  // this is now safe
  *p;

  p[1]; // but not that one

  return 0;
}

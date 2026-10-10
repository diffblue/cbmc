int main()
{
  const char *p;
  __CPROVER_size_t i;
  __CPROVER_assume(__CPROVER_is_cstring(p + i));
  // this is now safe
  p[i];

  return 0;
}

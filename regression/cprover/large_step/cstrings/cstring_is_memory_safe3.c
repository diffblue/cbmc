int main()
{
  const char *p;
  __CPROVER_size_t i;
  __CPROVER_assume(__CPROVER_is_cstring(p + i));

  // this is now safe
  const unsigned char *unsigned_p = (const unsigned char *)p;
  unsigned_p[i];

  return 0;
}

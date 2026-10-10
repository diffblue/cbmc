int main()
{
  const char *p;
  __CPROVER_size_t i;
  __CPROVER_assume(__CPROVER_is_cstring(p + i));
  __CPROVER_assume(p[i] != 0);
  i++;
  __CPROVER_assert(__CPROVER_is_cstring(p + i), "property 1"); // passes

  return 0;
}

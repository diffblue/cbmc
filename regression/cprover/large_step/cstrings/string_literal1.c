int main()
{
  char *p = "0123";
  __CPROVER_assert(__CPROVER_is_cstring(p), "property 1");     // passes
  __CPROVER_assert(__CPROVER_is_cstring(p + 4), "property 2"); // passes
  // __CPROVER_assert(__CPROVER_is_cstring(p+5), "property 3"); // fails
  return 0;
}

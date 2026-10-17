int main()
{
  char buffer[100], *p, *q;
  buffer[10] = 0;
  p = buffer;
  __CPROVER_assert(__CPROVER_is_cstring(p), "property 1"); // passes
  __CPROVER_assert(__CPROVER_is_cstring(q), "property 2"); // fails
  return 0;
}

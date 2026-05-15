int main()
{
  char buffer[100], *p, *q;
  q = buffer; // take address
  buffer[10] = 0;
  *p = 123; // might point into buffer
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // fails
  return 0;
}

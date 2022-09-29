int main()
{
  char buffer[100];
  buffer[10] = 0;
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // passes
  return 0;
}

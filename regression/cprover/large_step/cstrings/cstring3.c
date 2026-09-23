int main()
{
  char buffer[100];
  buffer[10] = 0;                                               // establish
  buffer[10] = 1;                                               // wreck
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // fails
  return 0;
}

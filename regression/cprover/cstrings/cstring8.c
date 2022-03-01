int main()
{
  char buffer[100];
  int i;
  buffer[10] = 0;
  buffer[i] = 123;                                              // wrecks it
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // fails
  return 0;
}

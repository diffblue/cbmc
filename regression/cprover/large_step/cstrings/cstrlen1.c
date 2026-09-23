int main()
{
  char buffer[100];
  buffer[0] = 0;
  __CPROVER_assert(__CPROVER_cstrlen(buffer) == 0, "property 1"); // passes
  return 0;
}

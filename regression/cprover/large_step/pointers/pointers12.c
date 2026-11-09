int x = 123;

int main()
{
  int *p; // might alias x
  *p = 456;
  __CPROVER_assert(x == 123, "property 1"); // should fail
  return 0;
}

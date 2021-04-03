int main()
{
  int x;
  int *p = &x;
  *p = 42;
  __CPROVER_assert(x == 42, "assertion x == 42");
  return 0;
}

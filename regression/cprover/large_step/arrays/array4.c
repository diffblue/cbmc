int main()
{
  int a[100];
  int *p = a;
  __CPROVER_assert(p[23] == a[23], "property 1"); // should pass
  return 0;
}

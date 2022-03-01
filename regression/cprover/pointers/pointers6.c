int x;

int main()
{
  int *p, *q;
  p = &x;
  *p = 10;
  q = &x;
  __CPROVER_assert(*q == 10, "property 1"); // passes

  return 0;
}

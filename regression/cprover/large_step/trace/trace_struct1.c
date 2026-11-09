struct S
{
  int a, b, c;
} x, y;

int main()
{
  x.a = 123;
  x.b = 456;
  int *p = &x.c;
  *p = 789;
  __CPROVER_assert(0, "property 1");
}

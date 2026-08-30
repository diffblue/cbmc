struct S
{
  int a, b, c;
} x;

int main()
{
  struct S *p = &x;
  p->b = 123;
  __CPROVER_assert(0, "property 1");
}

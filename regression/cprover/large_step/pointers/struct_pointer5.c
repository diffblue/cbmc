struct S
{
  int x, y;
};

int main()
{
  struct S a;
  int *p = &a.y;
  *p = 123;
  __CPROVER_assert(a.y == 123, "property 1"); // should pass
  return 0;
}

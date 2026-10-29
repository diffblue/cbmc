struct S
{
  int x, y;
};

int main()
{
  struct S a;
  struct S *p = &a;
  __CPROVER_assert(p->x == a.x, "property 1"); // should pass
  return 0;
}

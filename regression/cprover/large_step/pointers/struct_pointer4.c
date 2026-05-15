struct S
{
  int x, y;
};

int main()
{
  struct S a, b;
  struct S *p = &a;
  *p = b;                                     // copy entire struct
  __CPROVER_assert(a.x == b.x, "property 1"); // should pass
  return 0;
}

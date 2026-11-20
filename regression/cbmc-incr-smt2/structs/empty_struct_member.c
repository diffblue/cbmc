struct E
{
};
struct S
{
  int a;
  struct E e;
  int b;
};
struct S g1, g2;

int main(void)
{
  int c, x, y;
  g1.a = x;
  g1.b = y;
  g2.a = y;
  g2.b = x;
  struct S *p = c ? &g1 : &g2;
  struct S t = *p;
  __CPROVER_assert(t.a == (c ? x : y), "member a");
  __CPROVER_assert(t.b == (c ? y : x), "member b");
  return 0;
}

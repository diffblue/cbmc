struct S
{
  int a[2];
  int b;
} g;

int main()
{
  g.b = 1;
  g.a[1] = 2;
  __CPROVER_assert(g.b == 1, "member");
  __CPROVER_assert(g.a[1] == 2, "array member");
  return 0;
}

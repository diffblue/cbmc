struct S
{
  int x;
  int a[2];
};
int main()
{
  int a[2][2], b[2][2];
  __CPROVER_assume(a[0][0] == b[0][0] && a[0][1] == b[0][1]);
  __CPROVER_assume(a[1][0] == b[1][0] && a[1][1] == b[1][1]);
  __CPROVER_assert(__CPROVER_equal(a, b), "nested arrays equal");

  struct S s[2], t[2];
  __CPROVER_assume(s[0].x == t[0].x && s[1].x == t[1].x);
  __CPROVER_assume(s[0].a[0] == t[0].a[0] && s[0].a[1] == t[0].a[1]);
  __CPROVER_assume(s[1].a[0] == t[1].a[0] && s[1].a[1] == t[1].a[1]);
  __CPROVER_assert(__CPROVER_equal(s, t), "arrays of structs equal");
  return 0;
}

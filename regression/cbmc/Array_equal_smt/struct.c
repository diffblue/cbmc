int nondet_int();
struct S
{
  int a[2];
};
int main()
{
  int x = nondet_int(), y = nondet_int(), z = nondet_int();
  __CPROVER_assume(y == z + 0 * x);
  struct S s1 = {{x, y}};
  struct S s2 = {{x, z}};
  __CPROVER_assert(__CPROVER_equal(s1, s2), "struct equal");
  return 0;
}

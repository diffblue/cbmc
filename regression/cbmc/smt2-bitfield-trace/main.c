unsigned nondet_u(void);
struct S
{
  unsigned bf : 3;
  unsigned other;
};
int main(void)
{
  struct S s;
  s.bf = nondet_u();
  s.other = 7;
  __CPROVER_assume(s.bf == 5);
  __CPROVER_assert(0, "show trace");
  return 0;
}

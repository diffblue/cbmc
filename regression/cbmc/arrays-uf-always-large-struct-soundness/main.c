struct S
{
  int d[65];
};

unsigned nondet_unsigned(void);

int main()
{
  struct S a[2];
  a[0].d[0] = 1;
  a[1].d[0] = 1;
  unsigned i = nondet_unsigned();
  __CPROVER_assume(i < 2);
  __CPROVER_assert(a[i].d[0] == 1, "");
}

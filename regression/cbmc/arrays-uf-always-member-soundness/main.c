struct S
{
  int d[1];
};

int nondet_int(void);

int main()
{
  struct S a[2];
  a[0].d[0] = 1;
  a[1].d[0] = 1;
  int i = nondet_int();
  __CPROVER_assume(i == 0 || i == 1);
  __CPROVER_assert(a[i].d[0] == 1, "");
}

int nondet_int();

int main()
{
  int x;
  int *p = nondet_int() ? (int *)0 : &x;
  *p = 42;
  __CPROVER_assert(x == 42, "cannot fail with assert-to-assume");
}

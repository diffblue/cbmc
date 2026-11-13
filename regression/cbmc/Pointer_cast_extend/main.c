int nondet_int(void);
unsigned nondet_unsigned(void);

int main(void)
{
  // signed int to wider pointer: sign-extends
  int i = nondet_int();
  __CPROVER_assume(i < 0 && i > -5);
  char *p1 = (char *)i;
  unsigned long u1 = (unsigned long)p1;
  __CPROVER_assert(
    u1 > 0xFFFFFFFFul, "signed int to wider pointer sign-extends");

  // unsigned int to wider pointer: zero-extends
  unsigned v = nondet_unsigned();
  __CPROVER_assume(v > 0x80000000u && v < 0x80001000u);
  char *p2 = (char *)v;
  unsigned long u2 = (unsigned long)p2;
  __CPROVER_assert(
    u2 < 0x100000000ul, "unsigned to wider pointer zero-extends");

  return 0;
}

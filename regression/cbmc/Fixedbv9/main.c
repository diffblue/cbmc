typedef __CPROVER_fixedbv[32][16] fix;
unsigned char nondet_uchar(void);

int main(void)
{
  unsigned char u = nondet_uchar();
  __CPROVER_assume(u >= 200);
  fix d = u;
  __CPROVER_assert(d > 0, "unsigned value converts to positive fixedbv");
  return 0;
}

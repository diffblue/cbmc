_Bool nondet_bool();

int main()
{
  __CPROVER_integer n = 2;
  _Bool b = nondet_bool();
  __CPROVER_assert(b, "fails for b == 0");
  return 0;
}

_Bool nondet_bool();

void main()
{
  __CPROVER_assert(0, "non-fatal assertion");

  if(nondet_bool())
  {
    int divisor = nondet_bool() ? 2 : 0;

    // possible division by zero
    int result = 10 / divisor;

    __CPROVER_assert(divisor == 2 || divisor == 0, "divisor value");
  }
  else
    __CPROVER_assert(0, "independent assertion");
}

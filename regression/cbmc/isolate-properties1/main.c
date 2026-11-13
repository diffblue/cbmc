int nondet_int(void);

int main()
{
  int x = nondet_int();
  // No single model violates both of the following assertions, so each of
  // the two traces has to come from a solver call of its own.
  __CPROVER_assert(x != 1, "not one");
  __CPROVER_assert(x != 2, "not two");
  __CPROVER_assert(x + 0 == x, "holds");
  return 0;
}

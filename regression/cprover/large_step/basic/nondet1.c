int nondet_int();

int main()
{
  int x, y;

  x = nondet_int();
  __CPROVER_assert(x == 20, "property 1"); // fails

  y = nondet_int();
  __CPROVER_assert(x == y, "property 2"); // fails

  return 0;
}

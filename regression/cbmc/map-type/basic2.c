__CPROVER_map(int, int) nondet_map();

int main()
{
  __CPROVER_map(int, int) my_map = nondet_map();

  __CPROVER_assume(my_map(1) == 10);
  __CPROVER_assume(my_map(2) == 20);

  // should pass
  __CPROVER_assert(my_map(1) == 10, "(1)");
  __CPROVER_assert(my_map(2) == 20, "(2)");

  // should fail
  __CPROVER_assert(my_map(0) == 10, "(0)");

  return 0;
}

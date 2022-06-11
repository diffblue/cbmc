int main()
{
  __CPROVER_map(int, int) my_map;

  my_map = __CPROVER_lambda
  {
    int i;
    i == 1 ? 10 : 20
  };

  // should pass
  __CPROVER_assert(my_map(1) == 10, "(1)");
  __CPROVER_assert(my_map(2) == 20, "(2)");

  // should fail
  __CPROVER_assert(my_map(0) == 10, "(0)");

  return 0;
}

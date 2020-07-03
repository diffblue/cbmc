void param_test_val(int array[], int x)
{
  array[1] = x;
}

void pass_param()
{
  int b[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

  param_test_val(b, 5);

  // This assertion should be true since b[0] is unmodified
  __CPROVER_assert(b[0] == 0, "b[0]==0");

  // This assertion should be true since b[1] can only have one value
  __CPROVER_assert(b[1] == 5, "b[1]==5");

  param_test_val(b, 6);

  // Both these assertions shoul be unknown since the domain for
  // param_test_val, x is TOP so we don't know what is written
  __CPROVER_assert(b[1] == 5, "b[1]==5");
  __CPROVER_assert(b[1] == 6, "b[1]==6");

  // b[0] is still not modified so this assertion should still be true
  __CPROVER_assert(b[0] == 0, "b[0]==0");
}
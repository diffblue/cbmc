void param_function(int *old_val, int new_val)
{
  *old_val = new_val;
}

void param_function_extra(int *old_val, int new_val)
{
  *old_val = new_val;
}

void test_param_function(int nondet)
{
  int a = 5;
  int b;
  __CPROVER_assert(a == 5, "a==5");
  if(nondet)
  {
    a = 6;
    b = 7;
    goto whatever;
  }
  param_function(&a, 10);
  param_function_extra(&b, 7);
whatever:
  __CPROVER_assert(a == 10, "a==10");
  __CPROVER_assert(b == 7, "b==7");
}
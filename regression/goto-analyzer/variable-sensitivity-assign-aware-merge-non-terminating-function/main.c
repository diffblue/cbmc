int non_terminating(int *a, int val)
{
  while(1)
  {
    a = val;
  }
  return a;
}

int non_terminating_extra(int *a, int val)
{
  while(1)
  {
    a = val;
  }
  return a;
}

void test_non_terminating()
{
  int one_val = 5;
  int second_val = 6;
  __CPROVER_assert(one_val == 5, "one_val==5");
  __CPROVER_assert(second_val == 6, "second_val==6");

  non_terminating(&one_val, 10);
  __CPROVER_assert(one_val == 10, "one_val==10");
  non_terminating_extra(&second_val, 12);
  __CPROVER_assert(second_val == 12, "second_val==12");
  non_terminating_extra(&second_val, 13);
  __CPROVER_assert(second_val == 13, "second_val==13");
}
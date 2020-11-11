int main()
{
  __CPROVER_rounding_mode = 1;
  // test single stepping
  int i = 1;
  i = 2;
  i = 3;
  int x;
  __CPROVER_assert(x == 42, "should fail");
  return 0;
}

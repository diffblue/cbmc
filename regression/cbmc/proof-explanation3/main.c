int main()
{
  int input;
  __CPROVER_assume(input >= 0);
  __CPROVER_assume(input < 100);
  int result = input + 1;
  __CPROVER_assert(result > 0, "result is positive");
  return 0;
}

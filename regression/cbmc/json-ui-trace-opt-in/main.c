int main()
{
  int x;
  __CPROVER_assert(x != 42, "should fail with a counterexample");
  return 0;
}

int main()
{
  int x;

  __CPROVER_assume(x >= 10);
  __CPROVER_assert(x >= 5, "property 1");  // should pass
  __CPROVER_assert(x >= 15, "property 2"); // should fail
}

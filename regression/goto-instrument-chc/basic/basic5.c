int main()
{
  int x;
  __CPROVER_bool c1 = (x >= 10);
  __CPROVER_bool c2 = (x >= 5);
  // clang-format off
  __CPROVER_assert(c1 ==> c2, "property 1"); // passes
  __CPROVER_assert(c2 ==> c1, "property 2"); // fails
  return 0;
}

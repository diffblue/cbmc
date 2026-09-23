int main()
{
  int x;
  __CPROVER_assume(x >= 2);
  __CPROVER_assert(x >= 2, "holds");    // passes
  __CPROVER_assert(x >= 3, "may fail"); // fails
}

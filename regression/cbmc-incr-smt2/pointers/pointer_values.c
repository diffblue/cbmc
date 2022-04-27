int main()
{
  int *a;
  int *b = 0;
  int *c;
  __CPROVER_assume(c != 0);

  __CPROVER_assert(
    a != b, "should fail because a can be any pointer val, including NULL");
  __CPROVER_assert(
    a != c, "should fail because a and c can point to same object");
}

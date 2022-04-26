int main()
{
  int *a;
  int *b;
  __CPROVER_assume(a == 0xDEADBEEF);

  __CPROVER_assert(a != b, "should fail as b can also be assigned 0xDEADBEEF");
}

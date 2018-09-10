
int main()
{
  int x;
  __CPROVER_assume(x >= 0);
  __CPROVER_assume(x <= 10);

  int y;
  __CPROVER_assume(y >= 5);
  __CPROVER_assume(y <= 15);

  __CPROVER_assume(y < x);

  __CPROVER_assert(y <= 10, "y <= 10");

  return 0;
}

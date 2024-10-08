int main()
{
  __CPROVER_rational x;
  __CPROVER_rational y;
  x = 6 / 10;
  y = 3 / 5;

  __CPROVER_assert(y + 1 != x, "should pass");
  __CPROVER_assert(y != x, "should fail");
}

int y;

int g(void)
{
  y = 2;
  return 0;
}

int main()
{
  int j = (y = 1) + g();
  __CPROVER_assert(j == 1, "the value of an assignment is the value stored");
  __CPROVER_assert(y == 1, "y == 1 regardless of evaluation order");
  return 0;
}

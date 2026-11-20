int other;

void f(int divisor)
{
  // possible division by zero
  int result = 10 / divisor;
}

int main()
{
  int divisor;
  f(divisor);
  __CPROVER_assert(other == 0, "after the return");
  return 0;
}

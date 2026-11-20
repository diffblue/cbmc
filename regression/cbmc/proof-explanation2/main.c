int main()
{
  int x = 5;
  int y = 10;
  __CPROVER_assert(x > 0, "x is positive");
  return 0;
}

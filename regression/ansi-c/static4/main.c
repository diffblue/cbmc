int main()
{
  int y = 42;
  static int x = y;

  __CPROVER_assert(x == 42, "local static");
}

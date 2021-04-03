int bar(int other)
{
  __CPROVER_assert(other == 4, "assertion other == 4");
  return other + 1;
}

int main()
{
  int x = 3;
  int y = bar(x + 1);
  __CPROVER_assert(y == 5, "assertion y == 5");
}

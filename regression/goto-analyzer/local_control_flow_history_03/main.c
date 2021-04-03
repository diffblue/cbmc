int main(int argc, char **argv)
{
  int total = 0;
  int n = 50;
  int i;

  for(i = 0; i < n; ++i)
  {
    total += i;
  }

  __CPROVER_assert(
    total == (n * (n - 1) / 2), "assertion total == (n * (n - 1) / 2)");

  return 0;
}

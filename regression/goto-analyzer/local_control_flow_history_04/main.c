int main(int argc, char **argv)
{
  int total;
  int n;
  int i;

  total = 0;
  n = 8;
  for(i = 0; i < n; ++i)
  {
    total += i;
  }

  // Unknown due to the limit on unwindings
  __CPROVER_assert(
    total == (n * (n - 1) / 2), "assertion total == (n * (n - 1) / 2)");

  // Condense down to one path...

  total = 0;
  n = 16;
  for(i = 0; i < n; ++i)
  {
    total += i;
  }

  // Creates a merge path but only one user of it
  __CPROVER_assert(
    total == (n * (n - 1) / 2), "assertion total == (n * (n - 1) / 2)");

  total = 0;
  n = 32;
  for(i = 0; i < n; ++i)
  {
    total += i;
  }

  // Provable
  __CPROVER_assert(
    total == (n * (n - 1) / 2), "assertion total == (n * (n - 1) / 2)");

  return 0;
}


int main()
{
  int x;
  __CPROVER_assert(x, "Nondeterministic int assert.");
  return 0;
}

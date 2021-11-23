
int main()
{
  int x;
  int y;
  if(y)
    y = x;
  else
    y = x;
  __CPROVER_assert(y == x, "Nondeterministic int assert.");
  return 0;
}

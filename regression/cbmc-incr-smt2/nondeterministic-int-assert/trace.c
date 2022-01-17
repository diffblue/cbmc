
int main()
{
  int x, y;
  if(x != 0)
    __CPROVER_assert(y != 4, "Assert of inequality to 4.");
  else
    __CPROVER_assert(y != 2, "Assert of inequality to 2.");
  int z = y;
  return 0;
}

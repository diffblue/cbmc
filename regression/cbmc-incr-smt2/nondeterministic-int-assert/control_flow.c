
int main()
{
  int x, y;
  if(x != 0)
  {
    y = 9;
  }
  else
  {
    y = 4;
  }
  int z = y;
  __CPROVER_assert(x != z, "Assert of integer equality.");
  return 0;
}

int main()
{
  int x;
  if(x == 0)
  {
    __CPROVER_assert(!x, "assertion !x");
  }
  return 0;
}

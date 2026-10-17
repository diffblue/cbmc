int main()
{
  int x = 123;
  int y = 0;

  while(1)
  {
    // forward-propagating x==123 and y==0 suffices
    __CPROVER_assert(x != 0, "property 1");
    x += y;
  }
}

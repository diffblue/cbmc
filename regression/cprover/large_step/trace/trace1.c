int main()
{
  int x, y;

  y = 0;

  if(x > y)
  {
    x++;
    __CPROVER_assert(x > y, "property 1"); // fails
  }
}

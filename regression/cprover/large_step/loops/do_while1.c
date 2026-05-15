int x;

int main()
{
  x = 10;

  do
  {
    x = 20;
  } while(x != 20);

  __CPROVER_assert(x == 20, "property 1"); // passes

  return 0;
}

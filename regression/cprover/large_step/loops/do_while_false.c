int x;

int main()
{
  do
  {
    x = 123;
  } while(0);

  __CPROVER_assert(x == 123, "property 1"); // passes

  return 0;
}

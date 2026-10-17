int x, y;

int main()
{
  x = 1;
  y = 2;
  __CPROVER_assert(x == 1, "property 1");
  return 0;
}

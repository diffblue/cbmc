int x, y;

int main()
{
  x = 1;
  y = 2;
  x = 3;
  __CPROVER_assert(0, "property 1");
  return 0;
}

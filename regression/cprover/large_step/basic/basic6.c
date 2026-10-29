int x;

int main()
{
  x = 1;
  x++;
  x++;
  x++;
  x++;
  __CPROVER_assert(x == 5, "property 1");
  return 0;
}

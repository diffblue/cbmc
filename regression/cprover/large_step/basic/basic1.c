int x;

int main()
{
  x = 1;
  __CPROVER_assert(x == 1, "property 1");
  return 0;
}

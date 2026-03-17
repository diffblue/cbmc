struct S
{
  int x;
  int y = 20;
};

int main()
{
  S s{5};
  __CPROVER_assert(s.x == 5, "x is 5");
  __CPROVER_assert(s.y == 20, "y uses default");
  return 0;
}

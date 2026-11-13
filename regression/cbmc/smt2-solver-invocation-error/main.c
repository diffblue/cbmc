int main()
{
  int x;
  __CPROVER_assert(x == 0, "x is zero");
  return 0;
}

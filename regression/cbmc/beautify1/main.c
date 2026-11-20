int main()
{
  int x;
  int y;
  if(x > 100 && y > x)
    __CPROVER_assert(0, "reachable");
  return 0;
}

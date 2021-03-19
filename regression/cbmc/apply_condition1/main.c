int main()
{
  int y;
  __CPROVER_bool x;
  if(x == (__CPROVER_bool)y)
  {
    __CPROVER_assert(0, "assertion 0");
  }
  return 0;
}

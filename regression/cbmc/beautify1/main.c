int main()
{
  int x;
  if(x > 0)
    __CPROVER_assert(x < 0, "should fail");
  return 0;
}

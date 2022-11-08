int main()
{
  int a;
  if(a > 0)
  {
    if(a > 10)
    {
      (void)a;
      goto out;
    }
  }
  __CPROVER_assert(a > 0, "should fail");
out:
  return 0;
}

static int target(int x)
{
  return x + 1;
}
int kernel_entry(void)
{
  return target(7);
}

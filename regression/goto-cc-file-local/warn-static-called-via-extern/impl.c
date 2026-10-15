static int _recv(int x)
{
  return x + 1;
}
int kernel_entry(void)
{
  return _recv(7);
}

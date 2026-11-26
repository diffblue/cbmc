// do_recv ends in "_recv" but is unrelated to the external recv.
static int do_recv(int x)
{
  return x + 1;
}
int kernel_entry(void)
{
  return do_recv(7);
}

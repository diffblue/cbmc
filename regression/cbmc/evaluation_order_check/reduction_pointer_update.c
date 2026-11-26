int x, y, *q = &x;

int redirect(void)
{
  q = &y;
  return 0;
}

int write(void)
{
  *q = 1;
  return 0;
}

int read(void)
{
  return y;
}

int main()
{
  int j = redirect() + write() + read();
  __CPROVER_assert(j == 0, "y is read before it is written");
  return 0;
}

int f()
{
  return 0;
}

int g()
{
  return 1;
}

int main()
{
  int (*h)(void);

  h = g;
  h = f;

  int r;
  r = h();
  assert(r == 1);

  return 0;
}

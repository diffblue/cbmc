int f()
{
  return 0;
}

int g()
{
  return 1;
}

int h()
{
  return 2;
}

int i()
{
  return 3;
}

int main()
{
  int r;

  r = f();
  assert(r == 1);

  r = h();
  assert(r == 3);
}

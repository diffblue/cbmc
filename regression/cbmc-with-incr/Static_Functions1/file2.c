// the following function collides
int f()
{
  static int local=2;
  return local;
}

int f2()
{
  return f();
}

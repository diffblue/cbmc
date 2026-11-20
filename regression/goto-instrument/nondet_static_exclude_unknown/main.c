int foo = 0;

int f()
{
  static int bar = 0;
  return bar;
}

int main()
{
  assert(foo == 0);
  assert(f() == 0);
  return 0;
}

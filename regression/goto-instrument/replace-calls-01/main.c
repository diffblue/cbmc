int f(int a)
{
  return a;
}

int g(int b)
{
  return b + 1;
}

int main()
{
  int r;

  r = f(0);
  assert(r == 1);
}

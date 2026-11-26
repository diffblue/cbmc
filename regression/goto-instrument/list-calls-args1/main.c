void undefined(int, int);
int defined(int x)
{
  return x;
}
int main()
{
  int v = 2;
  undefined(1, v + 1);
  void (*fp)(int, int) = undefined;
  fp(3, 4);
  return defined(v);
}

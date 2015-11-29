int f()
{
  static int s=0;
  s++;
  return s;
}

int g()
{
  int l=0;
  l++;
  return l;
}

int main()
{
  assert(f()==1); // first call to f
  assert(f()==2); // second call to f
  assert(g()==1); // first call to g
  assert(g()==1); // second call to g
}

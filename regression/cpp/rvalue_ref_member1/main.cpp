struct S
{
  int x;
  S(int v) : x(v)
  {
  }
};

void f(S &&s)
{
  int y = s.x;
  s.x = 10;
}

int main()
{
  return 0;
}

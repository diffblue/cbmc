// test default arguments

int f(int a, int b=2, int c=3)
{
  return c;
}

class X{
public:
  int g(int a, int b, int c=3);
};

int X::g(int a, int b, int c)
{
  return c;
}

int main()
{
  assert(f(1, 10, 100)==100);
  assert(f(1, 10)==3);
  assert(f(1)==3);

  X x;
  assert(x.g(1, 2)==3);
}

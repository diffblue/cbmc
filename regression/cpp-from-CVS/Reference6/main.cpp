class X
{
public:  
  int x;
  
  X():x(0)
  {
  }
};

X g, y;

X &r()
{
  return g;
}

int main()
{
  y.x=10;

  r()=y;
  
  assert(g.x==10);
}

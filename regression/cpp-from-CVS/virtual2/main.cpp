int g;

class X
{
public:
  virtual int f();
  
  int m;
};

int X::f()
{
  g=10;
  m=1;
}

class Y:public X
{
};

int main()
{
  Y y;
  
  y.f();
  
  assert(g==10);
}

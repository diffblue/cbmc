int g;

class A
{
public:
  virtual void f()
  {
    g=1;
  }
  
  int mA;
  
  A();
};

A::A()
{
}

class B: public A
{
public:
  B()
  {
    mB=1;
  }

  virtual void f()
  {
    g=2;
    mB=3;
  }
  
  int mB;
};

int main()
{
  B b;
  A *p;
  
  p=&b;
  
  p->f();
  
  assert(g==2);
  assert(b.mB==3);
}

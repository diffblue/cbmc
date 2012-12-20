#include <cassert>

class B
{
public:
  virtual int f() const;
};

class A: public B
{
public:
  int f() const;
};

int B::f() const
{
  return 0;
}


int A::f() const
{
  return 1;
}


int main()
{
  A a;
  B b = (B) a;
  B* pB = (B*) &a;
  assert(b.f()==0);
  assert(pB->f()==1);
  assert(a.f()==1);
}

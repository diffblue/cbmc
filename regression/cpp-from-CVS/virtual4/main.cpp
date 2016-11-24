#include <cassert>

class B
{
public:
  virtual int f() { return 0; }
};

class A: public B
{
public:
  int f() { return 1; }
};

int main()
{
  A a;
  assert(a.A::f()==1);
  assert(a.B::f()==0);
}

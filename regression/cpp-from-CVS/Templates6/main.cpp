#include <cassert>

int g;

template <class T>
struct A
{
  T t;
  ~A() { g++; }
};

struct B
{
  B() { g=10; }
  ~B() { g=20; }
};

struct C
{
  A<B> a;
};

struct D: A<B>
{
};

int main()
{
  {
    C c;
    assert(g==10);
  }

  assert(g==20);

  {
    D d;  
    assert(g==10);
  }

  assert(g==20);
}

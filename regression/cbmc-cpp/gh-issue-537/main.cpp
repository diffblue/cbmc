#include <assert.h>

class C
{
public:
  int x;

  C() : x(7)
  {
  }
};

C c1;

class D
{
public:
  int x = 7;
};

int main()
{
  assert(c1.x == 7); // regression: global object initialization

  C c2;
  assert(c2.x == 7); // regression: local object initialization via constructor

  D d;
  assert(d.x == 7); // regression: C++11 default member initialization

  return 0;
}
//#include <assert.h>
//#include <iostream>
struct A
{
  virtual int f(){return 1;}
  virtual int g(){return 1;}
};

struct B: A
{
  int f(){return 2;}
};

struct C: B
{
};

struct D: C
{
  int g(){return 3;}
};


int main()
{
  D d;

  assert(d.f() == 2);
  assert(d.g() == 3);
  assert(((C*)(&d))->f() == 2);
  assert(((B*)(&d))->g() == 3);
  assert(((B*)(&d))->f() == 2);
  assert(((B*)(&d))->g() == 3);
  assert(((A*)(&d))->f() == 2);
  assert(((A*)(&d))->g() == 3);
}

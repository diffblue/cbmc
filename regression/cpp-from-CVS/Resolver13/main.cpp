#include <cassert>

struct A
{
  A* operator->() { return this; }
  int one() { return 1; }
  int one(int &i){ i = 1;}
};

struct B: public A
{
  A* operator->(){ return this; }
};

int main()
{
  B b;
  assert(b->one() == 1);
}

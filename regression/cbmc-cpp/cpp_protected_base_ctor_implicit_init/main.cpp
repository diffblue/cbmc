// A protected base-class constructor is accessible to a derived class
// initializing its own base subobject ([class.access.base]/1): implicit
// base initialization from the derived constructor must be accepted.

#include <cassert>

struct base
{
protected:
  base() : tag(7)
  {
  }
  int tag;

public:
  int get() const
  {
    return tag;
  }
};

struct derived : base
{
  derived()
  {
  }
};

int main()
{
  derived d;
  assert(d.get() == 7);
  return 0;
}

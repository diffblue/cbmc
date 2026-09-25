// List-initialization of a non-aggregate class type selects a
// constructor by overload resolution (N5008 dcl.init.list/3,
// over.match.list).  When the class derives from a base and its own data
// members do not line up with the brace-init elements (here the elements
// are constructor arguments, not member initializers -- mirroring CBMC's
// own `struct_union_typet::componentt{name, type}`, where componentt
// derives from exprt), aggregate-style member assignment cannot apply,
// so the elements must be treated as constructor arguments.  This must
// be accepted, not rejected as an invalid conversion to the class.

#include <cassert>

struct base
{
  int sum;
  base() : sum(0)
  {
  }
};

struct comp : base
{
  comp() : base()
  {
  }
  comp(int x, int y)
  {
    sum = x + y;
  }
};

comp make()
{
  return {3, 4};
}

int main()
{
  comp c = make();
  assert(c.sum == 7);
  return 0;
}

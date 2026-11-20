// A class with base classes that also has its own data members and a
// user-provided constructor is not an aggregate; a braced-init-list
// selects a constructor by overload resolution (N5008 dcl.init.list/3,
// over.match.list).  Member-by-member aggregate assignment must not be
// used here: it would omit the base subobject and yield an incomplete
// struct value.  Exercised for both a value object and a const-reference
// parameter, including from a default-initialized base.

#include <cassert>

struct base
{
  int e;
  base() : e(100)
  {
  }
};

struct comp : base
{
  int a;
  int b;
  comp() : a(0), b(0)
  {
  }
  comp(int x, int y) : a(x), b(y)
  {
  }
};

int total(const comp &c)
{
  return c.e + c.a + c.b;
}

int main()
{
  comp c = {3, 4};
  assert(c.e == 100 && c.a == 3 && c.b == 4);
  assert(total({5, 6}) == 111);
  return 0;
}

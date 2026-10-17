// A namespace-scope object initialized with an accessible constructor
// must be accepted even when the (unused) default constructor is private
// (class.access): the default constructor is not the one selected.

#include <cassert>

struct X
{
  int v;
  explicit X(int n) : v(n)
  {
  }

private:
  X() : v(0)
  {
  }
};

X g(5);

int main()
{
  assert(g.v == 5);
  return 0;
}

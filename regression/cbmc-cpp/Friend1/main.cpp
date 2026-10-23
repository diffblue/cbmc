#include <cassert>
class C
{
public:
  C(int _base) : base(_base)
  {
  }

  typedef int T;

  friend int f()
  {
    T x = 1;
    return x;
  }

  // N5008 [basic.lookup.argdep]/4.2: found by argument-dependent lookup
  friend int g(const C &c)
  {
    return c.base;
  }

  int base;
};

// N5008 [dcl.meaning.general]/2.1: the friend declaration of f does not
// bind its name; this declaration does
int f();

int main()
{
  C c(1);

  assert(f() == 1);
  assert(g(c) == 1);
}

// A function that is a friend of the type may default-initialize a local
// object whose default constructor is otherwise private (class.access):
// this must be accepted.

#include <cassert>

struct X
{
  int v;

private:
  X() : v(7)
  {
  }
  friend int main();
};

int main()
{
  X x;
  assert(x.v == 7);
  return 0;
}

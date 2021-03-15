#include <cassert>

template <class T>
struct A
{
  T t;
};

struct B
{
  int i;
  B():i(0) { }
};

int main()
{
  A<B> a;
  assert(a.t.i == 0);
}

#include <cassert>

template<int C>
struct A{
  int func();
};

template<int C>
int A<C>::func()
{
  return C;
}

int main()
{
  A<12> a;
  assert(a.func() == 12);
}

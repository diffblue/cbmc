#include <cassert>

namespace A::B::C
{
int x = 42;
}

int main()
{
  assert(A::B::C::x == 42);
  return 0;
}

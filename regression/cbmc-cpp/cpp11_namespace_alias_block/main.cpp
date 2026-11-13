// Namespace alias in block scope
#include <cassert>

namespace A
{
namespace B
{
int x = 42;
}
} // namespace A

int main()
{
  namespace AB = A::B;
  assert(AB::x == 42);
}

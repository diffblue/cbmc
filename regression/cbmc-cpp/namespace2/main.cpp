#include <cassert>

namespace N
{
template <class T>
struct A
{
  T t;
  A(T t) : t(t)
  {
  }
};
} // namespace N

using N::A;

int main()
{
  A<bool> a(true);
  assert(a.t == true);
}

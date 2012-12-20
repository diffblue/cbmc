#include <cassert>

template<class T>
struct A
{
  T t;
  bool eq(const A<T>& ref) const
  {
    return ref.t == t;
  }
};

int main()
{
  A<int> a;
  a.t = 10;
  assert(a.eq(a));
}

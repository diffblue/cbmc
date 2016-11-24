#include <cassert>

template <unsigned N>
struct A
{
  static const unsigned n = N;
};

template <unsigned N>
struct B
{
  A<0+N> a;
};

int main()
{
  B<10> b;
  assert(b.a.n == 10);
}

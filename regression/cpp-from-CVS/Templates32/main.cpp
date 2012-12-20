#include <cassert>

enum argt { ONE, TWO };

template < argt V = TWO, class T = argt >
class A
{
  public:
  A():v(V){}
  T v;
};

int main()
{
  A<> a;
  assert (a.v == TWO);
  return 0;
}


#include <cassert>

template <class T>
struct A {
  bool True();
};

template <class t>
bool A<t>::True() { return true; }

int main()
{
  A<int> a;
  assert(a.True() == true);
}

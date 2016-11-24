#include <cassert>

template <class T>
struct A{
  T i;
  void write(T i){this->i = i;}
};

struct B: A<bool>
{
  void write(bool i)
  {
    A<bool>::write(i);
  }
};

int main()
{
  B b;
  b.write(true);
  assert(b.i == true);
}

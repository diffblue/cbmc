#include <cassert>

template<typename T>
class X
{
public:
  // the :: should trigger elaboration of Z<int>
  enum { e = T::e };
};

template<typename T>
class Y:public X<T>
{
public:
  enum { e = X<T>::e } ;
};

template<typename T>
class Z
{
public:
  enum { e = 1 };
};

Y<Z<int> > y;

int main()
{
  assert(y.e==1);
}

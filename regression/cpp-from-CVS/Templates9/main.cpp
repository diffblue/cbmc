#include <cassert>

template <class T>
struct A {
  static const int a = 0;
};

// specialization to int
template <>
struct A<int> {
  static const int a = 1;
};

// specialization to char
template <>
struct A<char> {
  static const int a = 2;
};

// specialization to signed char
template <>
struct A<signed char> {
  static const int a = 3;
};

// specialization to unsigned char
template <>
struct A<unsigned char> {
  static const int a = 4;
};

int main()
{
  A<bool> obj0; // general one
  assert(obj0.a == 0);
  
  A<int> obj1; // specialized
  assert(obj1.a == 1);

  A<char> obj2; // specialized
  assert(obj2.a == 2);

  A<signed char> obj3; // specialized
  assert(obj3.a == 3);

  A<unsigned char> obj4; // specialized
  assert(obj4.a == 4);
}

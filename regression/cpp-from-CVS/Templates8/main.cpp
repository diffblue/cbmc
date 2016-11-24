#include <cassert>

template <class T>
struct A
{
  static T some_function(T v) { return v; }
};

int main()
{
  int v = A<int>::some_function(10);
  assert(v==10);  
}

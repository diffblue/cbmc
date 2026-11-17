#include <cassert>

// A member function of a class may name a protected member of a base
// class on an object of any derived type ([class.access.base]/5.4),
// not only through `this`.  Here the static member function
// base<derived>::sum accesses the protected member `data`, which it
// declares, on objects of the derived type `derived`.

template <class D>
struct base
{
protected:
  int data;

public:
  static int sum(D *arr, int n)
  {
    int s = 0;
    for(int i = 0; i < n; i++)
      s += arr[i].data;
    return s;
  }
};

struct derived : base<derived>
{
  void set(int x)
  {
    data = x;
  }
};

int main()
{
  derived d[2];
  d[0].set(3);
  d[1].set(4);
  assert(derived::sum(d, 2) == 7);
}

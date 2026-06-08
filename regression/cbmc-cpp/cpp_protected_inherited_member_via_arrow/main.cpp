#include <cassert>

// Accessing an inherited protected member through an overloaded
// operator-> must be access-checked at the actual point of use (the
// member function base<derived>::get), not from within the class that
// defines operator->.  Resolving operator-> enters that class's scope;
// the subsequent member access must not be checked from there.

template <class T>
struct wrap
{
  T *p;
  T *operator->() const
  {
    return p;
  }
};

template <class D>
struct base
{
protected:
  int data;

public:
  static int get(wrap<D> w)
  {
    return w->data;
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
  derived d;
  d.set(42);
  wrap<derived> w{&d};
  assert(base<derived>::get(w) == 42);
}

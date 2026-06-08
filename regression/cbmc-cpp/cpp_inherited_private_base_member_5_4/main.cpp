#include <cassert>

// [class.access.base]/5.4: a private member of a base class is
// accessible from a member function of that base even when named
// through an object of a derived type, where the member is otherwise
// inaccessible.  Here base<derived>::call names the private base member
// `secret` on an object of the derived type.

template <class D>
struct base
{
private:
  int secret() const { return 7; }

public:
  static int call(D &d) { return d.secret(); }
};

struct derived : base<derived>
{
};

int main()
{
  derived d;
  assert(base<derived>::call(d) == 7);
}

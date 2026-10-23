// Access control is per-class, not per-object ([class.access]/2): a
// member function of `W` may access the private members of *any* `W`
// object, including one named through an explicit object.  This must be
// accepted.

#include <cassert>

struct W
{
  explicit W(int v) : secret(v)
  {
  }

  int peek(const W &o) const
  {
    return o.secret;
  }

private:
  int secret;
};

int main()
{
  W a(3), b(5);
  assert(a.peek(b) == 5);
  return 0;
}

// Access control is judged at the point of use ([class.access]): the
// enclosing class/function in which the name appears, not the class of
// the object through which the member is named.  Here `C::bad` names the
// private base member `B::s` through an explicit object.  `C` derives
// from `B` but a derived class cannot access a *private* base member, so
// this is ill-formed and must be rejected -- even though the access is
// through an object whose static type (`B`) is the member's own class.

struct B
{
private:
  int s() const
  {
    return 1;
  }
};

struct C : B
{
  int bad(C &other)
  {
    return other.s();
  }
};

int main()
{
  C a, b;
  return a.bad(b);
}

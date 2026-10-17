// N5008 [class.access.base]/4.2: in a member of D, D's private base B is
// accessible, so `B::head(t)' converts the D & argument to B &.  Access is
// judged at the point of use ([class.access.general]/6), not in the scope
// of B that the qualified name designates.  libstdc++'s
// _Tuple_impl::_M_head calls _Head_base::_M_head this way.
extern "C" void __CPROVER_assert(bool, const char *);

struct B
{
  int v = 5;
  static int &head(B &b)
  {
    return b.v;
  }
};

struct D : private B
{
  static int &head(D &t)
  {
    return B::head(t);
  }
};

int main()
{
  D d;
  D::head(d) = 7;
  __CPROVER_assert(D::head(d) == 7, "qualified call through private base");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

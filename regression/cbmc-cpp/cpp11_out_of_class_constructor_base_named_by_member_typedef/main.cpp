// N5008 [class.base.init]/2: a mem-initializer-id denotes a base class if it
// names a class type that is a direct base -- here through a typedef that is
// a member of the class; [class.mfct]/1, [basic.scope.class]: names in an
// out-of-class member definition are looked up in the class's scope.  The
// mem-initializers of an out-of-class constructor definition were resolved
// in the enclosing namespace scope ("symbol 'my_base' is unknown"; CBMC's
// own full_array_abstract_objectt, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
template <class D, class K>
struct base
{
  int k;
  base(int x) : k(x + sizeof(K))
  {
  }
  base(const int &e, int)
  {
    k = e;
  }
};
struct kind
{
  char c[10];
};
class derived : public base<derived, kind>
{
public:
  typedef base<derived, kind> my_base;
  derived(int x);
  derived(const int &e, int n);
};
derived::derived(int x) : my_base(x)
{
}
derived::derived(const int &e, int n) : my_base(e, n)
{
}
int main()
{
  derived d(1);
  __CPROVER_assert(
    d.k == 11, "out-of-class definition, base named by member typedef");
  derived e(7, 0);
  __CPROVER_assert(e.k == 7, "second constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

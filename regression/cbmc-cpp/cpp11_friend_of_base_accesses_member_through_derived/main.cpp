// N5008 [class.access.base]/5.4: a member m of a base class B of the naming
// class N is accessible at R if B is accessible at R and m is accessible at
// R when named in B.  A friend of B may therefore use B's protected (and
// private) members on an object of a class derived from B.  The front end
// checked only N's friends: `d.as_base()' in a friend of base was rejected
// (in a template's decltype, a substitution failure: libc++'s
// __variant_detail::__visitation::__base, a friend of __ctor, naming
// `__impl().__as_base()', so std::visit found no __make_fmatrix).
extern "C" void __CPROVER_assert(bool, const char *);
struct base
{
protected:
  int as_base()
  {
    return 7;
  }
  friend struct visitor;
};
struct derived : base
{
};
struct visitor
{
  static int direct(derived &d)
  {
    return d.as_base();
  }
  template <class T>
  static int deduced(T &t)
  {
    return t.as_base();
  }
  template <class T>
  static decltype(sizeof(T)) in_decltype(T &t)
  {
    return sizeof(decltype(t.as_base()));
  }
};
struct holder
{
private:
  int secret = 3;
  friend int peek();
};
struct holder_derived : holder
{
};
int peek()
{
  holder_derived h;
  return h.secret;
}
int main()
{
  derived d;
  __CPROVER_assert(visitor::direct(d) == 7, "friend of the base");
  __CPROVER_assert(visitor::deduced(d) == 7, "in a template");
  __CPROVER_assert(visitor::in_decltype(d) == sizeof(int), "in decltype");
  __CPROVER_assert(peek() == 3, "private member of the base");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

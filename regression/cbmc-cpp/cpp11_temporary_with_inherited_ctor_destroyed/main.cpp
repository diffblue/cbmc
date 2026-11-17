// N5008 [class.dtor]/14, [class.temporary]/4: the temporary that
// `make(...)' returns is destroyed at the end of the full-expression, and
// with it its subobjects.  The class (constructed through constructors
// inherited from a base named by an alias template, [namespace.udecl]/1)
// is named by no variable, so its implicitly-defined destructor, a
// deferred member of the class template specialization, was never
// instantiated: the temporary was destroyed by a call to a function
// without a body, and tupish's destructor never ran.
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
template <class... T>
struct tupish
{
  int n;
  ~tupish()
  {
    ++destroyed;
  }
  template <class... U>
  tupish(U... u) : n(static_cast<int>(sizeof...(U)))
  {
  }
};
template <class Op, class... Bound>
struct pf_impl
{
  tupish<Bound...> bound_;
  template <class... A>
  pf_impl(A... a) : bound_(a...)
  {
  }
};
// the alias-template qualifier, as in libc++'s __perfect_forward
template <class Op, class... Bound>
using pf = pf_impl<Op, Bound...>;
struct takeish
{
};
template <class Fn, class B>
struct bb : pf<int, Fn, B>
{
  using pf<int, Fn, B>::pf;
};
template <class Fn, class... A>
auto make(Fn f, A... a) -> bb<Fn, int>
{
  return bb<Fn, int>(f, 0);
}
int main()
{
  __CPROVER_assert(
    make(takeish(), 5).bound_.n == 2, "alias-qualified inherited ctor");
  __CPROVER_assert(destroyed >= 1, "the temporary is destroyed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

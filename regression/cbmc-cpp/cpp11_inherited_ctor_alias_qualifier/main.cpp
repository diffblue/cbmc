// N5008 [namespace.udecl]/1 + [class.qual]/2: `using pf<...>::pf;` where
// `pf` is an ALIAS TEMPLATE for pf_impl -- the qualifier resolves to the
// base class, and the terminal name spells the qualifier's own last
// identifier, so this names the base's constructors ([class.qual]/2).
// Pre-fix the textual base-name comparison missed the alias, the
// constructor import silently never happened, and construction collapsed
// to default-initialization (wrong-code: assertion FAILURE).  The libc++
// __perfect_forward shape.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T> struct tupish
{
  int n;
  template <class... U> tupish(U... u) : n(static_cast<int>(sizeof...(U)))
  {
  }
};
template <class Op, class... Bound> struct pf_impl
{
  tupish<Bound...> bound_;
  template <class... A> pf_impl(A... a) : bound_(a...)
  {
  }
};
// the alias-template qualifier, as in libc++'s __perfect_forward
template <class Op, class... Bound> using pf = pf_impl<Op, Bound...>;
struct takeish
{
};
template <class Fn, class B> struct bb : pf<int, Fn, B>
{
  using pf<int, Fn, B>::pf;
};
template <class Fn, class... A> auto make(Fn f, A... a) -> bb<Fn, int>
{
  return bb<Fn, int>(f, 0);
}
int main()
{
  __CPROVER_assert(
    make(takeish(), 5).bound_.n == 2, "alias-qualified inherited ctor");
  return 0;
}

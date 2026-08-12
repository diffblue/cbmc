// N5008 [class.inhctor.init]/1 + [conv.ptr]/3: `bb<...>(f, 0)` names the
// DERIVED class; the inherited base constructor TEMPLATE (via
// `using pf<...>::pf;`) initializes the pf base subobject of a bb
// temporary -- the temporary's type is bb.  Pre-fix the temporary was
// typed pf, the enclosing return's conversion to bb failed, and the
// calling function template was silently dropped (call havocked:
// wrong-code).  Distilled from libc++ __bind_back_t under the ranges
// views::take pipe.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T> struct tupish
{
  int n;
  template <class... U> tupish(U... u) : n(static_cast<int>(sizeof...(U)))
  {
  }
};
template <class Op, class... Bound> struct pf
{
  tupish<Bound...> bound_;
  template <class... A> pf(A... a) : bound_(a...)
  {
  }
};
template <class Fn, class B> struct bb : pf<int, Fn, B>
{
  using pf<int, Fn, B>::pf;
};
template <class Fn, class... A> auto make(Fn f, A... a) -> bb<Fn, int>
{
  return bb<Fn, int>(f, 0);
}
struct takeish
{
};
int main()
{
  __CPROVER_assert(make(takeish(), 5).bound_.n == 2, "inherited ctor into member pack");
  return 0;
}

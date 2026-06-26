// N5008 [temp.variadic]/4,5 + [class.base.init]: a variadic constructor whose
// trailing parameter pack is empty in the recursion base must expand that pack
// to ZERO parameters, and its base/member initializers must construct each
// subobject.  This mirrors libstdc++'s _Tuple_impl recursive constructor
//   _Tuple_impl(_Head h, _Tail... t) : _Inherited(t...), _Base(h) { }
// for a two-element tuple.
//
// KNOWN BUG: instantiating the recursion base TImpl<1,int> (whose own Tail is
// empty) leaves the constructor parameter pack `Tail... tail` as a spurious
// void parameter and the empty-pack base-initializer unresolved, so the whole
// specialization -- and the derived TImpl<0,int,int> -- fail to construct;
// even head0 is not initialized.  The desired behaviour below therefore does
// not yet hold.  Flip to CORE once variadic constructor parameter-pack
// expansion handles the empty recursion-base pack.
//
// Non-vacuous: operands are nondet so the passing assertions are not folded,
// and assertion 3 is a deliberately wrong claim that must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <unsigned long I, typename H>
struct HeadBase
{
  H h;
  HeadBase() : h(0) {}
  HeadBase(H x) : h(x) {}
};

template <unsigned long, typename...>
struct TImpl;

template <unsigned long I>
struct TImpl<I>
{
  TImpl() {}
};

template <unsigned long I, typename Head, typename... Tail>
struct TImpl<I, Head, Tail...> : HeadBase<I, Head>, TImpl<I + 1, Tail...>
{
  TImpl(Head head, Tail... tail)
    : TImpl<I + 1, Tail...>(tail...), HeadBase<I, Head>(head)
  {
  }
};

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  TImpl<0, int, int> t(a, b);
  __CPROVER_assert(static_cast<HeadBase<0, int> &>(t).h == a, "head0 == a");
  __CPROVER_assert(static_cast<HeadBase<1, int> &>(t).h == b, "head1 == b");
  __CPROVER_assert(static_cast<HeadBase<1, int> &>(t).h == a, "WRONG must FAIL");
  return 0;
}

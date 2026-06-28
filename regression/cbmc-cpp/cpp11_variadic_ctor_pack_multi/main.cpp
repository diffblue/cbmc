// N5008 [temp.variadic]/5: a variadic constructor whose trailing parameter
// pack has TWO OR MORE elements must expand the pack to one parameter per
// element, and a pack expansion in the member-initializer arguments must
// expand likewise.  This mirrors the recursion step of libstdc++'s _Tuple_impl
// for a three-element std::tuple:
//   _Tuple_impl(_Head h, _Tail... t) : _Inherited(t...), _Base(h)
// where, at the top level, _Tail is a two-element pack.
//
// KNOWN BUG: a parameter pack of two or more elements is not expanded -- the
// single-element case happens to work by substituting the pack with its one
// element type, but the multi-element case leaves the constructor unusable, so
// the construction of TImpl<0,int,int,int> silently fails and main is
// truncated (the assertions are dropped, so verification passes vacuously).
// Flip to CORE once multi-element parameter-pack expansion is implemented.
//
// Non-vacuous: operands are nondet and assertion 2 is a deliberately wrong
// claim that must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <unsigned long I, typename H>
struct HeadBase
{
  H h;
  HeadBase(const H &x) : h(x) {}
  static H &M_head(HeadBase &b) { return b.h; }
};

template <unsigned long, typename...>
struct TImpl;

template <unsigned long I>
struct TImpl<I>
{
  TImpl() {}
};

template <unsigned long I, typename Head, typename... Tail>
struct TImpl<I, Head, Tail...> : TImpl<I + 1, Tail...>, HeadBase<I, Head>
{
  typedef HeadBase<I, Head> _Base;
  typedef TImpl<I + 1, Tail...> _Inherited;
  TImpl(const Head &h, const Tail &... t) : _Inherited(t...), _Base(h) {}
  static Head &M_head(TImpl &t) { return _Base::M_head(t); }
};

template <unsigned long I, typename Head, typename... Tail>
Head &get_helper(TImpl<I, Head, Tail...> &t)
{
  return TImpl<I, Head, Tail...>::M_head(t);
}

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = nondet_int();
  TImpl<0, int, int, int> t(a, b, c);
  __CPROVER_assert(get_helper<2>(t) == c, "third element forwarded");
  __CPROVER_assert(get_helper<2>(t) == a, "WRONG must FAIL");
  return 0;
}

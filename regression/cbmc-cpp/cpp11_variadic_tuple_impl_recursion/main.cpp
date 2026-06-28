// N5008 [temp.spec.partial.match], [temp.variadic]/5: end-to-end construction
// of a three-level recursive trailing-pack partial specialization in the exact
// shape of libstdc++'s _Tuple_impl -- a recursive partial spec
// `TImpl<I, Head, Tail...>` deriving from `TImpl<I+1, Tail...>` and a per-level
// `HeadBase<I, Head>`, whose constructor forwards the trailing pack to the base
// subobject via `Inherited(forward<Tail>(t)...)`.
//
// This exercises, together: selecting the recursive partial spec for THREE or
// more type arguments (trailing-pack matching), instantiating the recursive
// base `TImpl<I+1, Tail...>` to its full deduced arity (base-specifier pack
// expansion), replicating the multi-element constructor parameter pack, and
// forwarding it through the member-initializer.  Each element must land in its
// own HeadBase subobject.
//
// Header-free and non-vacuous: operands are nondet and assertion 3 is a
// deliberately wrong claim that must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <class T>
T &&fwd(T &x)
{
  return static_cast<T &&>(x);
}

template <unsigned long I, typename H>
struct HeadBase
{
  H val;
  HeadBase(H &&h) : val(h) {}
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
  typedef TImpl<I + 1, Tail...> Inherited;
  typedef HeadBase<I, Head> Base;
  TImpl(Head &&h, Tail &&... t) : Inherited(fwd<Tail>(t)...), Base(fwd<Head>(h)) {}
};

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = nondet_int();
  TImpl<0, int, int, int> t(fwd<int>(a), fwd<int>(b), fwd<int>(c));
  __CPROVER_assert(static_cast<HeadBase<0, int> &>(t).val == a, "element 0 in HeadBase<0>");
  __CPROVER_assert(static_cast<HeadBase<2, int> &>(t).val == c, "element 2 in HeadBase<2>");
  __CPROVER_assert(static_cast<HeadBase<2, int> &>(t).val == a, "WRONG must FAIL");
  return 0;
}

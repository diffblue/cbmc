// N5008 [temp.variadic]/16 and /9: a member-initializer pack expansion written
// purely by the function-parameter name -- `Inherited(t...)` rather than the
// libstdc++ `_Inherited(std::forward<_Tail>(__tail)...)` idiom -- must expand
// to the deduced arity, including the empty list at the recursion terminator.
//
// This is the recursive _Tuple_impl shape with a by-name forwarding
// constructor `TImpl(const Head&, const Tail&... t) : Inherited(t...), Base(h)`.
// Constructing a three-element instance must place each element in its own
// HeadBase subobject; the recursion terminates when Tail is empty, where
// `Inherited(t...)` becomes `Inherited()`.
//
// Header-free and non-vacuous: operands are nondet, assertion 3 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <unsigned long I, typename H>
struct HeadBase
{
  H val;
  HeadBase(const H &h) : val(h) {}
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
  TImpl(const Head &h, const Tail &... t) : Inherited(t...), Base(h) {}
};

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = nondet_int();
  TImpl<0, int, int, int> t(a, b, c);
  __CPROVER_assert(static_cast<HeadBase<0, int> &>(t).val == a, "element 0");
  __CPROVER_assert(static_cast<HeadBase<2, int> &>(t).val == c, "element 2");
  __CPROVER_assert(static_cast<HeadBase<2, int> &>(t).val == a, "WRONG must FAIL");
  return 0;
}

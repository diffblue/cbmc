// N5008 [class.base.init], [temp.variadic]: a constructor member-initializer
// may name a base class by a *template-id* whose arguments mention the class's
// own template parameters -- the recursion step of a _Tuple_impl-shaped class
// written without an `_Inherited` typedef:
//   TupleImpl(const Head&, const Tail&... t)
//     : TupleImpl<I+1, Tail...>(t...), HeadBase<I,Head>(h)
// The base-id `TupleImpl<I+1, Tail...>` must denote the base subobject
// (`TupleImpl<1, int, int>` for the top level), with `I+1` evaluated and the
// pack expanded.
//
// Regression: CBMC previously failed to resolve this template-id
// member-initializer (the non-type argument `I+1` was left with an
// unsubstituted `I`, and the pack collapsed), left the member_initializer
// unconverted, and aborted in goto-symex with "Invariant: Unreachable".
//
// Header-free and non-vacuous: operands are nondet and assertion 3 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <unsigned long I, typename H>
struct HeadBase
{
  H val;
  HeadBase(const H &h) : val(h) {}
  static const H &head(const HeadBase &b) { return b.val; }
};

template <unsigned long, typename...>
struct TupleImpl;

template <unsigned long I>
struct TupleImpl<I>
{
  TupleImpl() {}
};

template <unsigned long I, typename Head, typename... Tail>
struct TupleImpl<I, Head, Tail...> : TupleImpl<I + 1, Tail...>, HeadBase<I, Head>
{
  // base-id named directly as a template-id (no _Inherited typedef)
  TupleImpl(const Head &h, const Tail &... t)
    : TupleImpl<I + 1, Tail...>(t...), HeadBase<I, Head>(h)
  {
  }
};

template <unsigned long I, typename Head, typename... Tail>
const Head &get(const TupleImpl<I, Head, Tail...> &t)
{
  return HeadBase<I, Head>::head(t);
}

template <typename... T>
struct Tuple : TupleImpl<0, T...>
{
  Tuple(const T &... a) : TupleImpl<0, T...>(a...) {}
};

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = nondet_int();
  Tuple<int, int, int> t(a, b, c);
  __CPROVER_assert(get<0>(t) == a, "get<0>");
  __CPROVER_assert(get<2>(t) == c, "get<2>");
  __CPROVER_assert(get<2>(t) == a, "WRONG must FAIL");
  return 0;
}

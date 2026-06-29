// N5008 [temp.deduct.type]: function-template argument deduction of a trailing
// parameter pack from an argument whose type is an instance of a class
// template that has partial specializations.  This is the deduction underlying
// libstdc++'s `std::get` / `__get_helper`, which deduces `_Head, _Tail...` from
// a `_Tuple_impl<__i, _Head, _Tail...>` argument.
//
// `W<0,int,int,int>` is selected via the recursive partial specialization
// `W<I,Head,Tail...>`.  Its recorded template arguments must be the full list
// <0,int,int,int> so that deduction of `first<0>(w)` / `ntail<0>(w)` binds a
// TWO-element `Tail = <int,int>`.  Previously a partial-spec instance recorded
// the trailing pack collapsed to a single element, so deduction saw a
// truncated pack: the function template either failed to match or bound the
// wrong arity.
//
// Header-free and non-vacuous: operand is nondet and assertion 3 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

template <unsigned long, typename...>
struct W;

template <unsigned long I>
struct W<I>
{
};

template <unsigned long I, typename H, typename... Tl>
struct W<I, H, Tl...>
{
  H head;
  W(const H &h) : head(h) {}
};

// Deduce H and the (here two-element) trailing pack Tl from the argument.
template <unsigned long I, typename H, typename... T>
const H &first(const W<I, H, T...> &w)
{
  return w.head;
}

template <unsigned long I, typename H, typename... T>
int ntail(const W<I, H, T...> &)
{
  return (int)sizeof...(T);
}

int main()
{
  int a = nondet_int();
  W<0, int, int, int> w(a);
  __CPROVER_assert(first<0>(w) == a, "head value deduced through trailing pack");
  __CPROVER_assert(ntail<0>(w) == 2, "trailing pack has two elements");
  __CPROVER_assert(first<0>(w) == a + 1, "WRONG must FAIL");
  return 0;
}

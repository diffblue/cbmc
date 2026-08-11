// libc++ __bind_back_op shape: the mid/trailing-pack overload
// `operator()(_Fn, _BoundArgs...)` reached through TWO nested
// decltypes (invoke_'s F()() over pf's Op()(Idx...)).  Ties together
// the round-34 pack fixes: multi-pack replay, pack_expr splice,
// empty-pack strip with the own-pack constraint.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, T...> struct integer_sequence;
template <long... I> using index_sequence = integer_sequence<unsigned long, I...>;
struct op
{
  template <class F, class B, class...> int operator()(F, B...)
  {
    return 7;
  }
};
template <class...> struct pf;
template <class Op, long... Idx> struct pf<Op, index_sequence<Idx...>>
{
  template <class...> auto operator()() -> decltype(Op()(Idx...))
  {
    return Op()(Idx...);
  }
};
struct bb : pf<op, index_sequence<0, 1>>
{
} c;
template <class F> decltype(F()()) invoke_(F f)
{
  return f();
}
int main()
{
  __CPROVER_assert(invoke_(c) == 7, "mid param pack in decltype");
  return 0;
}

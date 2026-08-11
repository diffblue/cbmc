// N5008 [temp.names]/2 + [temp.variadic]/5: `get<Idx>...` — a pack
// expansion whose pattern is a bare fn-template-id VALUE (function
// pointer), parsed in an ambiguous `<` context (id-less
// template-arguments child).  The expanded elements must resolve as
// template-ids.  Pre-fix: symex invariant violation via the dropped
// member and malformed initialiser.  Distilled from libc++
// __perfect_forward under the ranges views::take pipe.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, T...> struct integer_sequence;
template <long... I> using index_sequence = integer_sequence<unsigned long, I...>;
template <long N> int get()
{
  return static_cast<int>(N);
}
struct op
{
  int operator()(int (*a)(), int (*b)())
  {
    return a() * 10 + b();
  }
};
template <class...> struct pf;
template <class Op, long... Idx> struct pf<Op, index_sequence<Idx...>>
{
  template <class...> auto operator()() -> decltype(Op()(get<Idx>...))
  {
    return Op()(get<Idx>...);
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
  __CPROVER_assert(invoke_(c) == 1, "fn-ptr template-id pack expansion");
  return 0;
}

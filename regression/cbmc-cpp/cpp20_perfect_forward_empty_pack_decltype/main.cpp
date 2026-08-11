// N5008 [temp.variadic]/7 + [temp.arg.explicit]/4: a member template
// `operator()(Args... args) -> decltype(Op()(Idx..., args...))` whose own
// pack deduces EMPTY under an outer deduction (`invoke_`'s
// decltype(F()())): the empty pack's dead reference must vanish from the
// trailing return type in every candidate-signature and instantiation
// copy, and the mixed-level expansion must not size `args...` by the
// unrelated non-empty class-level pack Idx.  Distilled from libc++
// __perfect_forward under std::invoke (ranges views::take pipe).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, T...> struct integer_sequence;
template <long... I> using index_sequence = integer_sequence<unsigned long, I...>;
struct op
{
  int operator()(long, long)
  {
    return 7;
  }
};
template <class...> struct pf;
template <class Op, long... Idx> struct pf<Op, index_sequence<Idx...>>
{
  template <class... Args>
  auto operator()(Args... args) -> decltype(Op()(Idx..., args...))
  {
    return Op()(Idx..., args...);
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
  __CPROVER_assert(invoke_(c) == 7, "mixed pack under outer deduction");
  return 0;
}

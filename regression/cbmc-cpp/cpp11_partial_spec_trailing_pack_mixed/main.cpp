// N5008 [temp.variadic]/5: same shape with the trailing pack NON-empty
// ({int, char}): the packaging spliced only pack_args_map, so the
// non-type pack Idx kept a single scalar element ({0} instead of {0,1}).
// clang++-validated; g++ rejects the alias-template pack deduction shape.
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
template <class Op, long... Idx, class... Bound>
struct pf<Op, index_sequence<Idx...>, Bound...>
{
  template <class...> auto operator()() -> decltype(Op()(Idx...))
  {
    return Op()(Idx...);
  }
};
struct bb : pf<op, index_sequence<0, 1>, int, char>
{
} c;
template <class F> decltype(F()()) invoke_(F f)
{
  return f();
}
int main()
{
  __CPROVER_assert(invoke_(c) == 7, "nonempty trailing pack partial spec");
  return 0;
}

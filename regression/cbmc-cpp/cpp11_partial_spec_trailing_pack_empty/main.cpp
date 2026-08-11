// N5008 [temp.variadic]/5,7: partial specialization
// `pf<Op, index_sequence<Idx...>, Bound...>` with the trailing type pack
// deduced EMPTY and a non-type pack deduced {0,1}.  The stored instance's
// flat argument replay bound nothing (multi-pack split unreconstructed),
// leaving `Idx` unbound in member signatures.  Distilled (cvise) from
// libc++ __perfect_forward under the ranges views::take closure.
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
struct bb : pf<op, index_sequence<0, 1>>
{
} c;
template <class F> decltype(F()()) invoke_(F f)
{
  return f();
}
int main()
{
  __CPROVER_assert(invoke_(c) == 7, "empty trailing pack partial spec");
  return 0;
}

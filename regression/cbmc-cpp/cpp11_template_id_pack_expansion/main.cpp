// N5008 [temp.variadic]/5: `get<Idx>()...` — a call-argument pack
// expansion whose pattern names the ENCLOSING class instance's
// non-type pack inside a template-id.  Pre-fix wrong-code: the pack
// name was scalar-substituted with a broken constant at member
// instantiation, the body was dropped, and the call returned havoc
// (4097 instead of 1).  Distilled from libc++ __perfect_forward.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, T...> struct integer_sequence;
template <long... I> using index_sequence = integer_sequence<unsigned long, I...>;
template <long N> int get()
{
  return static_cast<int>(N);
}
struct op
{
  int operator()(int a, int b)
  {
    return a * 10 + b;
  }
};
template <class...> struct pf;
template <class Op, long... Idx> struct pf<Op, index_sequence<Idx...>>
{
  template <class...> auto operator()() -> decltype(Op()(get<Idx>()...))
  {
    return Op()(get<Idx>()...);
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
  __CPROVER_assert(invoke_(c) == 1, "template-id pack expansion");
  return 0;
}

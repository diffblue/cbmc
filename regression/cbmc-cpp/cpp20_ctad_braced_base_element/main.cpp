// N5008 [over.match.class.deduct]/1.8 + [dcl.init.aggr]/2.2: aggregate
// CTAD where the single PARENTHESIZED argument is a BRACED temporary of
// the base-element's type: `closure(takeish{n})` deduces closure<takeish>
// and initializes the base element from the temporary.  The paren-arg
// variant (a function-call result instead of a braced temporary) works
// (cpp17/round-48 fixes); with the braced temporary the construction
// dies HARD in the auto-return deduction path with "unexpected
// expression: struct" -- a raw struct type node reaches expression
// type-checking through the return-value CTAD hook, and the whole
// translation unit fails (rejects-valid).
// clang++ accepts and runs clean; g++ rejects the base-element
// deduction shape.
extern "C" void __CPROVER_assert(bool, const char *);
template <class F> struct closure : F
{
};
struct takeish
{
  int n_;
  auto operator()(int n)
  {
    return closure(takeish{n});
  }
};
template <class F, class... A>
decltype(F()(A()...)) probe(F, A...);
template <class F, class... A> struct invokable
{
  using result = decltype(probe(F(), A()...));
};
int main()
{
  invokable<takeish, int>::result r = takeish{}(4);
  __CPROVER_assert(r.n_ == 4, "decltype through auto-return CTAD");
  return 0;
}

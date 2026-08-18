// N5008 [expr.type.conv] + [temp.variadic]/5: expanding `A()...` (a
// functional cast over the pack) inside a member alias's decltype
// (`using result = decltype(probe(F(), A()...))`, the libc++
// __invokable_r shape) substitutes the pack element INTO THE CALLEE
// SLOT as a raw type; the call node must be re-formed as the
// functional cast `int()`.  Previously the raw type node reached
// expression type-checking ("unexpected expression: signedbv"), the
// alias never formed, and the enclosing function was dropped.
extern "C" void __CPROVER_assert(bool, const char *);
struct takeish
{
  int n_;
};
struct taker
{
  auto operator()(int n)
  {
    return takeish{n};
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
  invokable<taker, int>::result r = taker{}(4);
  __CPROVER_assert(r.n_ == 4, "alias probe");
  return 0;
}

// N5008 [temp.arg.type], [temp.variadic]/7: in `derived<void>' the argument
// `void' is bound to R and the pack A is empty; the base-specifier
// `base<R, A...>' names base<void>.  The front end represents an empty pack
// by trailing `void' sentinels and stripped every trailing `void' argument,
// so base<void> became base<> and failed: "'base' is a template; thus,
// expected template arguments" (libstdc++'s
// _Maybe_unary_or_binary_function<_Res, _ArgTypes...>, the base of every
// std::function<void()>; CBMC's own contracts/utils.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.arg.type], [temp.variadic]/7: in base<void> the argument void
// is bound to R; only the arguments of the (here empty) pack A contribute
// nothing
template <typename R, typename... A>
struct base
{
  int tag = 7;
  int arity = sizeof...(A);
};
template <typename R, typename... A>
struct derived : base<R, A...>
{
};
int main()
{
  derived<void> d;
  derived<void, int, char> e;
  __CPROVER_assert(d.tag == 7 && d.arity == 0, "base<void> with an empty pack");
  __CPROVER_assert(e.arity == 2, "base<void, int, char>");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

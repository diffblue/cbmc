// N5008 [dcl.fct.spec]/3 (C++20): with explicit(constant-expression) the
// function is explicit iff the converted expression is true.  W<false>'s
// constructor is a converting constructor, so `take(5)' copy-initializes
// the parameter; W<true>'s is explicit.  The parser skipped the condition
// and made every such constructor explicit: "found no match for symbol
// 'take'" (the shape of std::pair's, std::tuple's and std::optional's
// conditionally explicit constructors).
extern "C" void __CPROVER_assert(bool, const char *);
template <bool E>
struct W
{
  int v;
  explicit(E) W(int x) : v(x)
  {
  }
};
int take(W<false> w)
{
  return w.v;
}
int main()
{
  W<true> a(1);
  __CPROVER_assert(take(5) == 5 && a.v == 1, "explicit(false) converts");
  __CPROVER_assert(
    __is_convertible(int, W<false>) && !__is_convertible(int, W<true>),
    "explicit(true) does not");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

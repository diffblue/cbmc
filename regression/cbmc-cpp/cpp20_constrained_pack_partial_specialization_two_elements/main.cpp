extern "C" void __CPROVER_assert(bool, const char *);
// [temp.spec.partial.match]/2-3: P<int, char, char> matches the constrained
// pack specialization (Args = {char, char}); the single-argument one does
// not match two arguments
template <class A, class... Args>
struct P
{
  static constexpr int v = 0;
};
template <class A, class... Args>
  requires(sizeof(A) > 0)
struct P<A, Args...>
{
  static constexpr int v = 1;
};
template <class A, class Arg>
  requires(sizeof(A) > 0)
struct P<A, Arg>
{
  static constexpr int v = 2;
};
int main()
{
  __CPROVER_assert(P<int, char>::v == 2, "one element");
  __CPROVER_assert(P<int, char, char>::v == 1, "two elements");
  __CPROVER_assert(P<int, char, char>::v != 1, "WRONG (must FAIL)");
}

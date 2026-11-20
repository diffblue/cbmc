extern "C" void __CPROVER_assert(bool, const char *);
// [temp.deduct.call]/3, [expr.type]/1: for a forwarding reference T &&, an
// xvalue argument of type char (static_cast<char &&>(c)) deduces T = char
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
template <class T>
T g(T &&);
int main()
{
  char c = 0;
  __CPROVER_assert(
    same<decltype(g(static_cast<char &&>(c))), char>::value, "xvalue");
  __CPROVER_assert(same<decltype(g(c)), char &>::value, "lvalue");
  __CPROVER_assert(same<decltype(g('c')), char>::value, "prvalue");
  __CPROVER_assert(
    !same<decltype(g(static_cast<char &&>(c))), char>::value,
    "WRONG (must FAIL)");
}

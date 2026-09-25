// N5008 [expr.prim.req.general]/3-4: the parameters of a requires-expression
// are in scope in its requirements, wherever the expression appears -- here a
// namespace-scope static_assert, not a concept definition.  The parameters
// were bound only while a concept was evaluated, so every requirement naming
// one was "invalid" and the assertion failed.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int x;
  void f();
  S operator+(const S &) const;
};
static_assert(
  requires(S s) { s.x; },
  "member");
static_assert(
  requires(S s) { s.f(); },
  "member function call");
static_assert(
  requires(S a, S b) { a + b; },
  "two parameters");
static_assert(
  requires(S s) {
    typename S;
    s.x;
  },
  "type and simple requirement");
static_assert(
  requires { typename S; },
  "no parameters");
template <class U>
concept HasX = requires(U u)
{
  u.x;
};
static_assert(HasX<S>, "concept, still");
int check(S s)
{
  static_assert(
    requires(S t) { t.x; }, "block scope");
  return requires(S t)
  {
    t.f();
  }
  ? 1 : 0;
}
int main()
{
  S s{1};
  __CPROVER_assert(check(s) == 1, "requires-expression as a value");
  __CPROVER_assert(check(s) == 0, "WRONG (must FAIL)");
}

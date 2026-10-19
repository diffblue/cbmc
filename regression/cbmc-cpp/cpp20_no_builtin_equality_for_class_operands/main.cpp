extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int x;
};
struct with_eq
{
  int x;
  bool operator==(const with_eq &o) const
  {
    return x == o.x;
  }
};
struct convertible
{
  int x;
  operator int() const
  {
    return x;
  }
};
// N5008 [expr.eq]/2, [expr.rel]/2: no built-in equality or relational
// operator takes operands of class type; without an operator function
// ([over.match.oper]/3) `a == b' is ill-formed, so the requirement is not
// satisfied ([expr.prim.req.simple]/1).  A conversion function to an
// arithmetic type reaches a built-in candidate ([over.built]).
template <class T>
constexpr bool has_eq = requires(const T &a, const T &b)
{
  a == b;
};
template <class T>
constexpr bool has_lt = requires(const T &a, const T &b)
{
  a < b;
};
int main()
{
  __CPROVER_assert(!has_eq<S> && !has_lt<S>, "class without operators");
  __CPROVER_assert(has_eq<with_eq> && !has_lt<with_eq>, "operator==");
  __CPROVER_assert(has_eq<convertible> && has_lt<convertible>, "conversion");
  __CPROVER_assert(has_eq<S>, "WRONG (must FAIL)");
  return 0;
}

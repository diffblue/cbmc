extern "C" void __CPROVER_assert(bool, const char *);
// [expr.rel]/2, [expr.eq]/1, [expr.log.and]/1, [expr.unary.op]/9: the
// comparison and logical operators yield bool, also as seen by auto,
// decltype and template argument deduction
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
int k(bool)
{
  return 1;
}
int k(int)
{
  return 2;
}
template <class T>
T id(T t)
{
  return t;
}
struct S
{
  bool operator==(const S &) const
  {
    return true;
  }
};
int main()
{
  int a = 1, b = 2;
  auto x = a < b;
  const auto y = !a;
  decltype(a && b) z = false;
  __CPROVER_assert(same<decltype(x), bool>::value, "auto from <");
  __CPROVER_assert(same<decltype(y), const bool>::value, "const auto from !");
  __CPROVER_assert(same<decltype(z), bool>::value, "decltype &&");
  __CPROVER_assert(same<decltype(a == b), bool>::value, "decltype ==");
  __CPROVER_assert(k(x) == 1 && k(id(a != b)) == 1, "overloads");
  __CPROVER_assert(same<decltype(id(a > b)), bool>::value, "deduced T");
  S s;
  auto e = s == s;
  __CPROVER_assert(e && same<decltype(e), bool>::value, "overloaded ==");
  auto f = [](int v) { return v > 0; };
  __CPROVER_assert(
    same<decltype(f(1)), bool>::value && f(1) && !f(0), "lambda");
  bool arr[2] = {a<b, a> b};
  auto g = arr[0];
  __CPROVER_assert(g && x && !y && !z, "values");
  __CPROVER_assert(!x, "WRONG (must FAIL)");
}

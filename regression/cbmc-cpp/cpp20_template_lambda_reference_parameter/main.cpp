extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [expr.prim.lambda.closure]/4: a generic lambda's closure type has a
// function call operator template whose template-parameter-list is the
// lambda's; `const T &' deduces T from the argument ([temp.deduct.call])
inline constexpr auto less_than = []<class T, class U>(const T &t, const U &u)
{ return t < u; };
int main()
{
  int v = 1;
  auto inc = []<class T>(const T &t) { return t + 1; };
  __CPROVER_assert(inc(v) == 2, "const T & parameter");
  __CPROVER_assert(less_than(1, 2.5), "two template parameters");
  __CPROVER_assert(inc(v) == 3, "WRONG (must FAIL)");
  return 0;
}

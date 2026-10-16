// N5008 [expr.prim.lambda.closure]/5: the function call operator of a
// closure type is constexpr if it satisfies the requirements; a call of it
// is a constant expression.  GCC 16's __literal_encoding_is_unicode calls
// a lambda in a consteval function (__do_vformat_to's default template
// argument).
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int plus_one(int y)
{
  auto f = [](int x) { return x + 1; };
  return f(y);
}
static_assert(plus_one(1) == 2, "lambda call");
template <unsigned U = plus_one(0)>
int g()
{
  return int(U);
}
int main()
{
  __CPROVER_assert(g() == 1, "default template argument");
  __CPROVER_assert(g() == 0, "WRONG (must FAIL)");
  return 0;
}

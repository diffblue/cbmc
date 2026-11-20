// N5008 [expr.const], [except.handle]: an exception thrown and caught in a
// constant expression.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int f()
{
  try
  {
    throw 3;
  }
  catch(int x)
  {
    return x;
  }
  return 0;
}
template <int V>
struct W
{
  static constexpr int value = V;
};
int main()
{
  __CPROVER_assert(
    W<f()>::value == 3,
    "an exception thrown and caught in a constant expression");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

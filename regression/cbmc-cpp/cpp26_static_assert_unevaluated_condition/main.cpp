// N5008 [dcl.pre]/13, [expr.const]/10.22: f() is a constant expression, as
// its exception object is destroyed within the evaluation, and its value is
// 3, so the static_assert fails and the program is ill-formed.
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
static_assert(f() == 4, "f() is 4");
int main()
{
}

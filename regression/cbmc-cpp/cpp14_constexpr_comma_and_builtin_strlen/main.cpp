// N5008 [expr.comma]/1: in a constant evaluation the left operand of a
// comma is evaluated and discarded, the value is the right operand's.
// GCC and clang evaluate __builtin_strlen in a constant expression.  Xcode
// 26's libc++ computes a string_view's length as
// `return ((void)0), _Traits::length(__s);' with
// char_traits<char>::length calling __builtin_strlen.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr int next(int x)
{
  return ((void)0), x + 1;
}
constexpr int assign_then(int x)
{
  return x = 3, x + 1;
}
constexpr unsigned long length(const char *s)
{
  return ((void)0), __builtin_strlen(s);
}

int main()
{
  static_assert(next(1) == 2, "void left operand");
  static_assert(assign_then(1) == 4, "left operand evaluated first");
  static_assert(length("UTF-32LE") == 8, "strlen");
  static_assert(length("") == 0, "empty");
  int n = 1;
  __CPROVER_assert(next(n) == 2, "run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// N5008 [dcl.pre]/13, [expr.const]/12: the condition of a static_assert is a
// constant expression; one that is not -- a call of a function that is not
// constexpr, a variable that is not usable in constant expressions --
// makes the program ill-formed, at namespace scope as in a block.  CBMC
// skipped such an assertion with a warning ("could not be evaluated") and
// verified the program.  g++ 13 and clang++ 18 reject it.
int f(int x)
{
  return x;
}
int g = 3;
static_assert(f(1) == 1, "non-constexpr call");
int main()
{
  static_assert(g == 3, "non-constant variable");
  return 0;
}

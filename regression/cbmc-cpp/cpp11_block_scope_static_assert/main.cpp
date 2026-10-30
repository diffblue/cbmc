// N5008 [dcl.pre]/10: a static_assert-declaration whose condition is false
// makes the program ill-formed -- at block scope as much as at namespace
// scope.  Block-scope failures were silently turned into a `skip'.
struct S
{
  int a;
  char b;
};
int main()
{
  static_assert(sizeof(S) == 8, "true, passes");
  static_assert(sizeof(int) == 3, "block-scope failure is diagnosed");
  return 0;
}

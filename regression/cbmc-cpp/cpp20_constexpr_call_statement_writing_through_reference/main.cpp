// N5008 [stmt.expr]/1, [dcl.constexpr]: a constexpr function's call statement
// may modify an object through a reference argument; f() is 2.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr void touch(int &x)
{
  x = 2;
}
constexpr int f()
{
  int x = 1;
  touch(x);
  return x;
}
int main()
{
  constexpr int v = f();
  __CPROVER_assert(v == 2, "write through reference argument");
  __CPROVER_assert(v == 1, "WRONG (must FAIL)");
}

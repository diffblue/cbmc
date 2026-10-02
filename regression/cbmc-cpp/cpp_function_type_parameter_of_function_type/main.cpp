extern "C" void __CPROVER_assert(bool, const char *);
int g()
{
  return 5;
}
// [dcl.fct]/5: a parameter of function type `void()' is adjusted to a
// pointer to function, so F is int(int (*)())
int cb(int (*h)())
{
  return h();
}
typedef int F(int());
int main()
{
  F *p = cb;
  __CPROVER_assert(p(g) == 5, "function-typed parameter");
  __CPROVER_assert(p(g) != 5, "WRONG (must FAIL)");
}

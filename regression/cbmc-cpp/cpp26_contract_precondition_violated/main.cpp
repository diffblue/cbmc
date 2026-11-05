// N5008 [dcl.contract.func], [basic.contract.eval]: a violated precondition.
extern "C" void __CPROVER_assert(bool, const char *);
int f(const int x) pre(x > 0)
{
  return x;
}
int main()
{
  int r = f(1);
  __CPROVER_assert(r == 1, "a call satisfying the precondition");
  // violates f's precondition: with the enforce semantic the program ends
  // here, so there is no WRONG assertion after it -- the precondition is
  // the property that must fail
  f(0);
  return 0;
}

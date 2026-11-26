// N5008 [dcl.fct.def.delete]: a deleted function with a reason.
extern "C" void __CPROVER_assert(bool, const char *);
int f(int) = delete("no int");
int f(double)
{
  return 1;
}
int main()
{
  __CPROVER_assert(f(1.0) == 1, "the other overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

// N5008 [expr.unary.noexcept], [lex.nullptr]: nullptr and the noexcept
// operator.
extern "C" void __CPROVER_assert(bool, const char *);
void f() noexcept
{
}
int main()
{
  int *p = nullptr;
  __CPROVER_assert(p == 0 && noexcept(f()), "nullptr and noexcept");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

// Test that block-scope declarations of __CPROVER_uninterpreted_*
// functions are handled correctly (not emitted as DECL/DEAD).
int main()
{
  int __CPROVER_uninterpreted_f(int);
  int x;
  __CPROVER_assume(x >= 0 && x <= 10);
  int y = __CPROVER_uninterpreted_f(x);
  __CPROVER_assert(
    __CPROVER_uninterpreted_f(x) == y,
    "uninterpreted function is deterministic");
  return 0;
}

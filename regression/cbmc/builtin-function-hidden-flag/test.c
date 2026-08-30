#include <assert.h>

// Regression test for #5207: a function hidden via __CPROVER_HIDE must keep its
// body hidden in traces, while its function-call and matching function-return
// events carry a consistent (here: visible) hidden flag, so a trace consumer
// can ignore internal steps yet still pair calls with returns.
int hidden_helper(int *p)
{
__CPROVER_HIDE:;
  *p = 1; // internal step: must remain hidden
  return *p;
}

int main()
{
  int x = 0;
  int r = hidden_helper(&x);
  assert(r == 0); // fails, producing a trace through hidden_helper
}

#include <assert.h>
#include <stdlib.h>

// A helper with its own contract-less loop (mirrors CBMC's built-in `memcmp`
// model, whose loop is unwound at solve time). Its locals `res`, `pa`, `pb`,
// and `k` are written inside the loop.
int cmp(const char *a, const char *b, unsigned n)
{
  int res = 0;
  const char *pa = a, *pb = b;
  for(unsigned k = 0; k < n; k++)
  {
    res += (*pa++) - (*pb++);
  }
  return res;
}

// Regression test: a call to a function containing a contract-less loop, made
// from inside an outer loop *with* a contract. The callee's loop locals must be
// scoped to the callee, not checked against the outer loop's assigns clause.
// Previously the assignability checks on `res`, `pa`, `pb`, and `k` failed
// spuriously (see the discussion in model-checking/kani#4790).
int main()
{
  unsigned n;
  __CPROVER_assume(1 <= n && n <= 4);
  char *buf = malloc(n);

  unsigned i = 0;
  while(i < n)
    // clang-format off
    __CPROVER_loop_invariant(i <= n)
    __CPROVER_decreases(n - i)
    // clang-format on
    {
      cmp(buf, buf, 1);
      i++;
    }

  assert(i == n);
  return 0;
}

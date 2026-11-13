// As loop_contracts_callee_with_loop, a callee containing a loop without a
// contract is called from a loop that has a contract. The callee's own locals,
// including the counter of its loop and a local declared in its loop body, are
// not visible to the caller and must not be checked against the caller's loop
// assigns clause. The callee's writes to globals must be: the write to `g` is
// covered by the clause, the write to `h` is not.
static unsigned g[4];
static unsigned h;

static void callee(unsigned v)
{
  unsigned a = 0;
  for(int k = 0; k < 3; k++)
  {
    unsigned b = v;
    a = a + b;
    h = a;
  }
  g[0] = a;
}

unsigned nondet_unsigned(void);

int main(void)
{
  unsigned n = nondet_unsigned();
  for(unsigned i = 0; i < n; i++)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_object_whole(g))
    __CPROVER_loop_invariant(i <= n)
    __CPROVER_decreases(n - i)
    // clang-format on
    {
      callee(i);
    }
  return 0;
}

// Minimal reproducer: --arrays-uf-always SAT soundness issue (large structs)
//
// With --arrays-uf-always, indexing an array of structs containing array
// members with 65+ elements through a nondeterministic index produces a
// spurious counterexample. The arrays2.patch fix in boolbv_index.cpp only
// addresses the inner array access; the outer array-of-structs access still
// goes through the array theory and fails for large structs.
//
// Fails:  cbmc --arrays-uf-always --no-standard-checks main.c
// Passes: cbmc --no-standard-checks main.c
// Passes: cbmc --smt2 --arrays-uf-always --no-standard-checks main.c
// Passes: with d[64] instead of d[65]
struct S
{
  int d[65];
};

unsigned nondet_unsigned(void);

int main()
{
  struct S a[2];
  a[0].d[0] = 1;
  a[1].d[0] = 1;
  unsigned i = nondet_unsigned();
  __CPROVER_assume(i < 2);
  __CPROVER_assert(a[i].d[0] == 1, "");
}

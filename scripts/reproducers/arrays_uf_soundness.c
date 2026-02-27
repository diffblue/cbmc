// Minimal reproducer: --arrays-uf-always SAT soundness issue
//
// With --arrays-uf-always, indexing an array of structs that contain array
// members through a nondeterministic index produces a spurious counterexample
// on the SAT backend. SMT + --arrays-uf-always verifies successfully.
//
// Fails:  cbmc --arrays-uf-always --no-standard-checks main.c
// Passes: cbmc --no-standard-checks main.c
// Passes: cbmc --smt2 --arrays-uf-always --no-standard-checks main.c
struct S
{
  int d[1];
};

int nondet_int(void);

int main()
{
  struct S a[2];
  a[0].d[0] = 1;
  a[1].d[0] = 1;
  int i = nondet_int();
  __CPROVER_assume(i == 0 || i == 1);
  __CPROVER_assert(a[i].d[0] == 1, "");
}

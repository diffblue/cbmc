// Minimal reproducer: --arrays-uf-always crash with array-of-structs
//
// Crash:    cbmc --arrays-uf-always arrays_uf_crash.c
// No crash: cbmc arrays_uf_crash.c
// No crash: cbmc --smt2 --arrays-uf-always arrays_uf_crash.c
//
// Invariant violation in src/solvers/flattening/arrays.cpp:563
// "unexpected array expression (add_array_constraints): 'member'"
//
// Note: the assertion itself is expected to fail (x is uninitialized).
// The bug is that CBMC crashes instead of reporting the failure.
struct S { int a[1]; };
int main() {
  struct S x[2];
  int i;
  __CPROVER_assume(i >= 0 && i < 2);
  __CPROVER_assert(x[i].a[0] == 0, "");
}

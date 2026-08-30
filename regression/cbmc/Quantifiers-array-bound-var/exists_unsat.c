int main()
{
  // Exercises the exists/assumption code path with an array-typed bound
  // variable (renaming runs before quantifier rewriting). The quantifier is
  // unsatisfiable (no array has a[0] < a[1] and a[1] < a[0]), so the
  // assumption blocks every path and the assertion is vacuously unreachable; a
  // dropped or mis-encoded array-typed bound variable would make it reachable
  // and fail.
  // clang-format off
  __CPROVER_assume(__CPROVER_exists { int a[3]; a[0] < a[1] && a[1] < a[0] });
  // clang-format on

  __CPROVER_assert(0, "unreachable: exists-assumption is unsatisfiable");

  return 0;
}

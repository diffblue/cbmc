int main()
{
  // A universal quantifier with an array-typed bound variable. Like
  // struct-typed bound variables, an array-typed bound variable must remain a
  // symbol rather than being decomposed into an array expression by field
  // sensitivity.
  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall { int a[3]; a[0] - a[0] == 0 },
    "holds for every array-typed bound variable");
  // clang-format on

  return 0;
}

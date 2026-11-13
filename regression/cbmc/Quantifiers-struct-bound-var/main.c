struct point
{
  int x;
  int y;
};

int main()
{
  // A universal quantifier with a struct-typed bound variable exercises the
  // assertion (forall) code path, where quantifier rewriting happens before
  // renaming. The struct-typed bound variable must remain a symbol rather than
  // being decomposed into a struct expression by field sensitivity.
  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall { struct point p; p.x - p.x == 0 },
    "holds for every struct-typed bound variable");
  // clang-format on

  return 0;
}

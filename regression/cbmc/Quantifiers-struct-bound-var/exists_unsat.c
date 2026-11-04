struct point
{
  int x;
  int y;
};

int main()
{
  // Discriminating companion to exists.c on the exists/assumption path: this
  // existential quantifier is unsatisfiable (no struct point p has p.x < p.y
  // and p.y < p.x), so the assumption blocks every path and the assertion
  // below is vacuously unreachable. If the struct-typed bound variable were
  // dropped or the exists mis-encoded during renaming, the assumption would no
  // longer block and the assertion would be reachable and fail.
  // clang-format off
  __CPROVER_assume(__CPROVER_exists { struct point p; p.x < p.y && p.y < p.x });
  // clang-format on

  __CPROVER_assert(0, "unreachable: exists-assumption is unsatisfiable");

  return 0;
}

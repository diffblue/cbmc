struct point
{
  int x;
  int y;
};

int main()
{
  // The body does not hold for every struct point (e.g. x != y), so
  // verification must fail. This confirms that the quantifier body is genuinely
  // evaluated rather than the quantifier being silently dropped.
  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall { struct point p; p.x == p.y },
    "does not hold for every struct-typed bound variable");
  // clang-format on

  return 0;
}

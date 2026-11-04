struct point
{
  int x;
  int y;
};

int main()
{
  // An existential quantifier with a struct-typed bound variable exercises the
  // assumption (exists) code path, where renaming happens before quantifier
  // rewriting. The struct-typed bound variable must remain a symbol rather than
  // being decomposed by field sensitivity during renaming.
  // clang-format off
  __CPROVER_assume(__CPROVER_exists { struct point p; p.x > p.y });
  // clang-format on

  __CPROVER_assert(1 == 1, "reachable after exists-assumption");

  return 0;
}

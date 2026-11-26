struct S
{
  int x, y;
};

int nondet_int(void);

int main()
{
  struct S a, b, t;
  int c = nondet_int();

  // A whole-struct value computed by an if-then-else must be assigned to t in
  // one go, rather than split into per-field assignments. See
  // assignment_constraint_rec / is_whole_struct_value.
  t = c ? a : b;

  __CPROVER_assert(c == c, "reachable");
  return 0;
}

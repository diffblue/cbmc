struct S
{
  int x, y;
};

int nondet_int(void);

int main()
{
  struct S a, b, t;
  int c = nondet_int();

  // Whole-struct if-assignment: t is stored as a single (datatype) value.
  t = c ? a : b;

  // Reading individual fields of t via their addresses must agree with the
  // per-branch field values. This exercises the bridge between the whole
  // struct value stored for t and the field-address reads of t.x / t.y.
  __CPROVER_assert(t.x == (c ? a.x : b.x), "field x after ternary");
  __CPROVER_assert(t.y == (c ? a.y : b.y), "field y after ternary");

  return 0;
}

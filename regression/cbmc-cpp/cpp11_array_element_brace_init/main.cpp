// N5008 [dcl.init.aggr]/2,5: the elements of a class array are initialized from
// the corresponding brace-enclosed initializer-clauses; an element without an
// initializer-clause is value-initialized.
//
// KNOWNBUG: for an element type with a user-provided constructor, the front-end
// wraps the per-element brace initializers `{ {args}, ... }` into an array
// expression whose element operands are never type-checked (they keep no type);
// during per-element construction that array is indexed, producing a nil-typed
// expression that later aborts simplification (an invariant violation in
// simplify_rec).  So `S a[N]{ {a}, {b} }` currently crashes rather than
// constructing each element from its brace-clause.  Flip to CORE once class
// array elements are constructed directly from their initializer-clauses.

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int v;
  S(int x) : v(x)
  {
  }
};

int main()
{
  S a[2]{{10}, {20}};

  __CPROVER_assert(a[0].v == 10, "first element from its brace-clause");
  __CPROVER_assert(a[1].v == 20, "second element from its brace-clause");
  return 0;
}

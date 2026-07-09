// N5008 [dcl.init.aggr]/2, [dcl.init.list]/3: the elements of a class array are
// initialized from the corresponding brace-enclosed initializer-clauses.  When
// the element type has a user-provided constructor it is not an aggregate, so
// each element is list-initialized by a constructor call; an element without an
// initializer-clause is value-initialized.
//
// Regression test for per-element brace-initialization of an array whose
// element type has a user-provided constructor (`S a[N]{ {args}, ... }`).
// Previously the front-end wrapped the brace elements into an array_exprt whose
// operands kept no type, which crashed symex; each element is now constructed
// in place from its own initializer-clause.  (Aggregate element types, whose
// brace elements are typecheckable aggregate literals, keep the array_exprt
// path -- see cpp11_array_element_brace_init_aggregate.)
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

static int ctor_count = 0;

struct S
{
  int v;
  S() : v(7)
  {
    ctor_count++;
  }
  S(int x) : v(x)
  {
    ctor_count++;
  }
};

int main()
{
  S a[3]{{10}, {20}}; // a[0]=S(10), a[1]=S(20), a[2] value-initialized => S()

  __CPROVER_assert(
    a[0].v == 10 && a[1].v == 20 && a[2].v == 7,
    "elements initialized from their brace-clauses; missing one value-inited");
  __CPROVER_assert(
    ctor_count == 3, "a constructor ran exactly once per element");
  __CPROVER_assert(a[2].v != 7, "WRONG must FAIL");
  return 0;
}

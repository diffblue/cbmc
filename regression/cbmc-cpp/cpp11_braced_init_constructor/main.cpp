// A class with a user-provided (converting) constructor is not an aggregate
// ([dcl.init.aggr]/1), so a braced-init-list must invoke a constructor
// ([dcl.init.list]/3.4), not perform member-wise aggregate initialization.
// Regression test: CBMC used to aggregate-initialize `Wrap w{x}` member-wise
// (assigning the int x to the int* member), producing a spurious "invalid
// implicit conversion" error.  A converting constructor whose single
// parameter is a reference to some *other* type must not be mistaken for a
// copy/move constructor.

struct Wrap
{
  int *ptr;
  explicit Wrap(int &r) : ptr(&r)
  {
  }
};

struct Pair
{
  int *a;
  long *b;
  Pair(int &x, long &y) : a(&x), b(&y)
  {
  }
};

int main()
{
  int x = 5;
  long y = 9;

  Wrap w{x}; // list-init -> Wrap(int&)
  __CPROVER_assert(w.ptr == &x, "braced converting-ctor (one arg)");

  Wrap w2(x); // direct-init -> Wrap(int&)
  __CPROVER_assert(w2.ptr == &x, "paren converting-ctor (one arg)");

  Pair p{x, y}; // list-init -> Pair(int&, long&)
  __CPROVER_assert(p.a == &x && p.b == &y, "braced multi-arg ctor");
  return 0;
}

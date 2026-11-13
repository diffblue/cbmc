// A struct reached through a pointer contains, by value, the struct holding
// the pointer. With SMT-LIB datatypes (--z3, --cvc5) the datatype of ring
// was not yet named when that of adapter was declared, and conversion
// aborted with map::at.

struct adapter;

// a ring points back to the adapter that contains it by value
struct ring
{
  struct adapter *adapter;
  int value;
};

struct adapter
{
  struct ring rings[2];
  int n;
};

int main(void)
{
  // an array indexed non-deterministically keeps its struct-typed elements,
  // so the datatype of ring has to be declared
  struct ring rings[2];
  unsigned i;
  __CPROVER_assume(i < 2);
  rings[i].adapter = 0;
  __CPROVER_assert(rings[i].adapter == 0, "holds");
  __CPROVER_assert(rings[i].value == 1, "nondeterministic");
  return 0;
}

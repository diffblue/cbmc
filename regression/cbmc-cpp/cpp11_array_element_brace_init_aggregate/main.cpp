// N5008 [dcl.init.aggr]: an array of an aggregate element type is initialized
// element-wise from the brace-enclosed initializer-clauses, each of which
// aggregate-initializes an element (recursively, including a nested array
// member).  The element type here has no user-provided constructor, so it is an
// aggregate even though its members are non-trivial in general.
//
// Companion to cpp11_array_element_brace_init: this exercises the aggregate
// element path (which must keep working -- it mirrors the src/util
// simplify_utils.cpp saj_table, an array of an aggregate `{ id, array }`).
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct T
{
  const int id;
  const int values[3];
};

const T table[] = {{1, {2, 3, 0}}, {4, {5, 0, 0}}};

int main()
{
  __CPROVER_assert(
    table[0].id == 1 && table[0].values[1] == 3 && table[1].id == 4 &&
      table[1].values[0] == 5,
    "aggregate array elements initialized member-wise, incl. nested array");
  __CPROVER_assert(sizeof(table) / sizeof(table[0]) == 2, "bound deduced to 2");
  __CPROVER_assert(table[1].id != 4, "WRONG must FAIL");
  return 0;
}

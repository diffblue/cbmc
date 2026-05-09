// Per [expr.type.conv]/2 and [dcl.init.list]/3.10:
// A functional-style cast with a braced-init-list of the form T{} (no
// elements) performs value-initialization.  For scalar types the
// result is zero.
//
// CBMC currently rejects T{} for primitive types with
//   "cannot initialize 'signed int' with an initializer list"
// at type-check time, producing a CONVERSION ERROR rather than
// recognising the empty brace-init-list as value-initialization.

int get_int()
{
  return int{};
}

double get_double()
{
  return double{};
}

int main()
{
  __CPROVER_assert(get_int() == 0, "int{} value-initializes to 0");
  __CPROVER_assert(get_double() == 0.0, "double{} value-initializes to 0.0");
  return 0;
}

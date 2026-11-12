int main()
{
  int x;
  int *p = &x;
  __CPROVER_size_t l = (__CPROVER_size_t)p;

  // Comparing a pointer with an integer other than a null pointer constant
  // violates a constraint (C11 6.5.8p2, 6.5.9p2); GCC and Clang accept it with
  // a warning and compare the pointer with the integer converted to a pointer.
  __CPROVER_assert(p == l, "equal");
  __CPROVER_assert(l <= p, "relational");

  // a null pointer constant does not warrant a warning
  __CPROVER_assert(p != 0, "null pointer constant");

  // enumerations and _Bool are integer types
  enum E
  {
    A
  } e = A;
  _Bool b = 0;
  int *q = 0;
  __CPROVER_assert(q == e, "enum");
  __CPROVER_assert(q == b, "_Bool");
  return 0;
}

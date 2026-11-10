// Per [temp.point] p1: when a function template is instantiated, the
// point of instantiation is located such that the definition (not
// just a forward declaration) is visible.  CBMC prefers a template's
// definition over a forward declaration with the same name when both
// are present in the parent scope.

// Forward declaration with no body.
template <class T>
T zero();

// Definition appears later in the same TU.
template <class T>
T zero()
{
  return 0;
}

int main()
{
  // If CBMC used the forward declaration instead of the definition,
  // the function would have no body and the return value would be
  // nondet — the assertion below would not hold.
  __CPROVER_assert(zero<int>() == 0, "zero<int> returns 0");
  __CPROVER_assert(zero<long>() == 0L, "zero<long> returns 0");
  return 0;
}

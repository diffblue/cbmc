int main()
{
  char *p, *q;
  // functional consistency of dynamic_object
  __CPROVER_assume(p == q);

  __CPROVER_assert(
    __CPROVER_DYNAMIC_OBJECT(p) == __CPROVER_DYNAMIC_OBJECT(q), "property 1");

  __CPROVER_assert(
    __CPROVER_DYNAMIC_OBJECT(p) == __CPROVER_DYNAMIC_OBJECT(q + 1),
    "property 2");
}

int main()
{
  void *p, *q;
  // functional consistency of object_size
  __CPROVER_assume(p == q);

  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(p) == __CPROVER_OBJECT_SIZE(q), "property 1");

  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(p) == __CPROVER_OBJECT_SIZE(q + 1), "property 2");
}

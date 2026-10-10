int main()
{
  char *p, *q;
  // functional consistency of live_object
  __CPROVER_assume(__CPROVER_LIVE_OBJECT(p));
  __CPROVER_assume(p == q);
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(q), "property 1");
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(q + 1), "property 2");
}

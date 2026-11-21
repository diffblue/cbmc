int main()
{
  int *p; // unconstrained, might point to itself!

  //__CPROVER_assume(!__CPROVER_same_object(p, &p));
  *p = 123; // can't point to itself
  int p_value = *p;
  __CPROVER_assert(p_value == 123, "property 1"); // should pass

  return 0;
}

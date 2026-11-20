int nondet_int();

int main()
{
  int i = nondet_int();
#ifdef __GNUC__
  if(i == 2)
  {
    __CPROVER_assert(i < 100, "before the assumption");
    // __builtin_types_compatible_p yields a proper "bool" typed constant,
    // which makes this an ASSUME false
    __CPROVER_assume(__builtin_types_compatible_p(double, float));
  }
#else
  __CPROVER_assume(i != 2);
#endif
  __CPROVER_assert(i != 2, "only reachable with i != 2");
  return 0;
}
